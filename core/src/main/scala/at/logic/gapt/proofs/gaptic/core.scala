package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ OccConnector, Sequent, SequentIndex }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.formats.babel.BabelSignature

import scalaz._
import Scalaz._
import Validation.FlatMap._

object ProofState {
  def apply( initialGoal: OpenAssumption ): ProofState =
    ProofState( initialGoal, List( initialGoal ), Map() )
  def apply( initialGoal: Sequent[( String, HOLFormula )] ): ProofState =
    ProofState( OpenAssumption( initialGoal ) )
}
case class ProofState private (
    initialGoal:      OpenAssumption,
    subGoals:         List[OpenAssumption],
    finishedSubGoals: Map[OpenAssumptionIndex, LKProof]
) {

  def isFinished: Boolean = subGoals.isEmpty

  def currentSubGoalOption: Option[OpenAssumption] = subGoals.headOption

  def replace( index: OpenAssumptionIndex, proofSegment: LKProof ): ProofState = {
    val subGoal = subGoals.find( _.index == index ).getOrElse(
      throw new IllegalArgumentException( s"Cannot replace non-existing open subgoal: $index" )
    )
    require(
      proofSegment.conclusion isSubsetOf subGoal.conclusion,
      s"Conclusion of proof segment is not a subset of subgoal:\n${proofSegment.conclusion}\nis not a subset of\n${subGoal.conclusion}"
    )

    val newOpenAssumptions = proofSegment.treeLike.postOrder.collect { case oa: OpenAssumption => oa }.distinct

    val subGoals_ = subGoals.filter( _.index != index ).diff( newOpenAssumptions )

    for ( ( idx, oas ) <- newOpenAssumptions.groupBy( _.index ) )
      require( oas.size == 1, s"Different new open assumptions with same index:\n${oas.mkString( "\n" )}" )
    require(
      newOpenAssumptions intersect subGoals_ isEmpty,
      s"New open assumption contains already open subgoal"
    )
    require(
      newOpenAssumptions.map( _.index ).toSet intersect finishedSubGoals.keySet isEmpty,
      s"New open assumption contains already finished subgoal"
    )

    copy(
      subGoals = newOpenAssumptions.toList ++ subGoals_,
      finishedSubGoals = finishedSubGoals + ( index -> proofSegment )
    )
  }

  def replace( proofSegment: LKProof ): ProofState = replace( subGoals.head.index, proofSegment )

  class ProofSegmentInsertionVisitor( failOnMissingSubgoal: Boolean ) extends LKVisitor[Unit] {
    override def visitOpenAssumption( p: OpenAssumption, dummy: Unit ): ( LKProof, OccConnector[HOLFormula], Unit ) = {
      finishedSubGoals.get( p.index ) match {
        case Some( segment ) =>
          val subProof = recurse( segment, () )._1
          require( subProof.conclusion multiSetEquals segment.conclusion )
          val segment_ = WeakeningContractionMacroRule( subProof, p.conclusion )
          require( segment_.conclusion multiSetEquals p.conclusion )
          ( segment_, OccConnector.guessInjection( segment_.conclusion, p.conclusion ).inv, () )
        case None if failOnMissingSubgoal  => throw new IllegalArgumentException( s"Subgoal still open: $p" )
        case None if !failOnMissingSubgoal => super.visitOpenAssumption( p, dummy )
      }
    }
  }

  def partialProof: LKProof = new ProofSegmentInsertionVisitor( failOnMissingSubgoal = false ).apply( initialGoal, () )
  def result: LKProof = new ProofSegmentInsertionVisitor( failOnMissingSubgoal = true ).apply( initialGoal, () )

  override def toString = toSigRelativeString
  def toSigRelativeString( implicit sig: BabelSignature ) =
    subGoals.map { _.toPrettyString }.mkString( "\n" )
}

/**
 * The globally unique index of an open assumption in a proof state.
 */
class OpenAssumptionIndex {
  override def toString = Integer toHexString hashCode() take 3
}

/**
 * Defines the case class open assumption which considers an arbitrary labelled sequence an axiom.
 */
case class OpenAssumption(
    labelledSequent: Sequent[( String, HOLFormula )],
    index:           OpenAssumptionIndex             = new OpenAssumptionIndex
) extends InitialSequent {
  override def conclusion = labelledSequent map { labelledFormula => labelledFormula._2 }

  def apply( label: String ): HOLFormula = labelledSequent.elements.find( _._1 == label ).get._2

  def toPrettyString( implicit sig: BabelSignature ) = {
    val builder = new StringBuilder
    for ( ( l, f ) <- labelledSequent.antecedent ) builder append s"$l: ${f.toSigRelativeString}\n"
    builder append ":-\n"
    for ( ( l, f ) <- labelledSequent.succedent ) builder append s"$l: ${f.toSigRelativeString}\n"
    builder.toString
  }
}

/**
 * Class that describes how a tactic should be applied: to a label, to the unique fitting formula, or to any fitting formula.
 */
sealed abstract class TacticApplyMode {
  def forall( p: String => Boolean ): Boolean
}

/**
 * Apply a tactic to a specific label.
 *
 * @param label The label that the tactic should be applied to.
 */
case class OnLabel( label: String ) extends TacticApplyMode {
  def forall( p: String => Boolean ): Boolean = p( label )
}

/**
 * Apply a tactic only if there is exactly one formula that fits.
 */
case object UniqueFormula extends TacticApplyMode {
  def forall( p: String => Boolean ): Boolean = true
}

/**
 * Apply a tactic if there is a formula that fits.
 */
case object AnyFormula extends TacticApplyMode {
  def forall( p: String => Boolean ): Boolean = true
}

case class TacticalFailure( tactical: Tactical[_], goal: Option[OpenAssumption], message: String ) {
  override def toString = toSigRelativeString
  def toSigRelativeString( implicit sig: BabelSignature ) =
    s"$tactical: $message:${goal.map( "\n" + _.toPrettyString ).getOrElse( "" )}"
}

trait Tactical[+T] { self =>
  def apply( proofState: ProofState ): ValidationNel[TacticalFailure, ( T, ProofState )]

  /**
   * Returns result of first tactical, if there is any,
   * else it returns the result of the second tactical,
   * with the possibility of no result from either.
   *
   * @param t2
   * @return
   */
  def orElse[S >: T]( t2: Tactical[S] ): Tactical[S] = {
    val t1 = this

    new Tactical[S] {
      override def apply( proofState: ProofState ) = {
        t1( proofState ) findSuccess t2( proofState )
      }
      override def toString = s"$t1 orElse $t2"
    }
  }

  def andThen[S]( t2: Tactical[S] ): Tactical[S] = new Tactical[S] {
    def apply( proofState: ProofState ) = self( proofState ) flatMap { x => t2( x._2 ) }
    override def toString = s"$self andThen $t2"
  }

  def map[S]( f: T => S ): Tactical[S] = new Tactical[S] {
    def apply( proofState: ProofState ) = self( proofState ) map { x => f( x._1 ) -> x._2 }
  }

  def flatMap[S]( f: T => Tactical[S] ): Tactical[S] = new Tactical[S] {
    def apply( proofState: ProofState ) = self( proofState ) flatMap { x => f( x._1 )( x._2 ) }
  }

  def onAllSubGoals: Tactical[Unit] = new Tactical[Unit] {
    def apply( proofState: ProofState ) = {
      type StrVal[T] = ValidationNel[TacticalFailure, T]
      Applicative[StrVal].traverse( proofState.subGoals )( subGoal => self.asTactic( subGoal ).map( subGoal.index -> _ ) ) map {
        _.foldRight( proofState ) { case ( ( index, subState ), state ) => state.replace( index, subState._2 ) }
      } map { x => ( (), x ) }
    }
    override def toString = s"$self.onAllSubGoals"
  }

  def asTactic: Tactic[T] = new Tactic[T] {
    def apply( goal: OpenAssumption ) = self( ProofState( goal ) ) map { case ( res, p ) => res -> p.partialProof }
    override def toString = s"$self.asTactic"
  }
}

trait Tactic[+T] extends Tactical[T] { self =>
  def apply( goal: OpenAssumption ): ValidationNel[TacticalFailure, ( T, LKProof )]

  override def apply( proofState: ProofState ): ValidationNel[TacticalFailure, ( T, ProofState )] =
    proofState.currentSubGoalOption match {
      case None => TacticalFailure( this, None, "no open subgoal" ).failureNel
      case Some( goal ) => this( goal ) map {
        case ( res, proofSegment ) =>
          res -> proofState.replace( goal.index, proofSegment )
      }
    }

  /**
   * Returns result of first tactic, if there is any,
   * else it returns the result of the second tactic,
   * with the possibility of no result from either.
   *
   * @param t2
   * @return
   */
  def orElse[S >: T]( t2: Tactic[S] ): Tactic[S] = {
    val t1 = this

    new Tactic[S] {
      override def apply( goal: OpenAssumption ) = {
        t1( goal ) findSuccess t2( goal )
      }

      override def toString = s"$t1 orElse $t2"
    }
  }

  def onAll[S]( t2: Tactical[S] ) = new Tactical[Unit] {
    def apply( proofState: ProofState ) = self( proofState ) flatMap { x => t2.onAllSubGoals( x._2 ) }
    override def toString = s"$self onAll $t2"
  }

  protected def findFormula( goal: OpenAssumption, mode: TacticApplyMode ): FindFormula =
    new FindFormula( goal, mode )
  protected class FindFormula( goal: OpenAssumption, mode: TacticApplyMode ) {
    type Val = ( String, HOLFormula, SequentIndex )

    def withFilter( pred: Val => Boolean ): ValidationNel[TacticalFailure, Val] =
      goal.labelledSequent.zipWithIndex.elements.collect {
        case ( ( l, f ), i ) if mode.forall { _ == l } && pred( l, f, i ) => ( l, f, i )
      } match {
        case Seq( f ) => f.success
        case Seq( someFormula, _* ) =>
          mode match {
            case AnyFormula => someFormula.success
            case _          => TacticalFailure( self, Some( goal ), s"Formula could not be uniquely determined." ).failureNel
          }
        case _ =>
          mode match {
            case OnLabel( l ) => TacticalFailure( self, Some( goal ), s"Label $l not found." ).failureNel
            case _            => TacticalFailure( self, Some( goal ), s"No matching formula found." ).failureNel
          }
      }

    def flatMap[U]( func: Val => ValidationNel[TacticalFailure, U] ): ValidationNel[TacticalFailure, U] =
      withFilter( _ => true ).flatMap( func )
  }
}

/**
 * Object that wraps helper function to generate new label from an existing one
 */
object NewLabels {
  /**
   * Actual helper function for a fresh variable.
   *
   * @param sequent
   * @param fromLabel
   * @return
   */
  def apply( sequent: Sequent[( String, HOLFormula )], fromLabel: String ): Stream[String] = {
    val regex = f"$fromLabel%s_([0-9]+)".r

    // Get integer subscripts (i.e 1, 2, 3 for x_1, x_2, x_3)
    val usedVariableSubscripts = {
      for ( ( label, _ ) <- sequent.elements; m <- regex findFirstMatchIn label )
        yield Integer parseInt ( m group 1 )
    }.toSet

    for ( i <- Stream from 0 if !usedVariableSubscripts( i ) ) yield f"$fromLabel%s_$i%d"
  }
}

object NewLabel {
  def apply( sequent: Sequent[( String, HOLFormula )], fromLabel: String ): String =
    NewLabels( sequent, fromLabel ).head
}