package at.logic.gapt.proofs.gaptic

import java.util.Locale

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLSequent, Sequent, SequentConnector, SequentIndex }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.utils.NameGenerator
import cats.syntax.all._
import cats.instances.all._

object guessLabels {
  def suggestLabel( formula: Formula, idx: SequentIndex, nameGen: NameGenerator ): String =
    formula match {
      case Const( name, _ ) => nameGen.fresh( name )
      case _ if idx.isSuc   => nameGen.fresh( "g" )
      case _ if idx.isAnt   => nameGen.freshWithIndex( "h" )
    }

  def apply( sequent: HOLSequent ): Sequent[( String, Formula )] = {
    val nameGen = new NameGenerator( Set() )
    for ( ( f, i ) <- sequent.zipWithIndex )
      yield suggestLabel( f, i, nameGen ) -> f
  }
}

object ProofState {
  def apply( initialGoal: OpenAssumption ): ProofState =
    ProofState( initialGoal, List( initialGoal ), Map() )
  def apply( initialGoal: Sequent[( String, Formula )] ): ProofState =
    ProofState( OpenAssumption( initialGoal ) )
  def apply( initialGoal: HOLSequent )( implicit dummyImplicit: DummyImplicit ): ProofState =
    apply( guessLabels( initialGoal ) )
  def apply( initialGoal: Formula ): ProofState =
    apply( Sequent() :+ initialGoal )
}
case class ProofState private (
    initialGoal:      OpenAssumption,
    subGoals:         List[OpenAssumption],
    finishedSubGoals: Map[OpenAssumptionIndex, LKProof] ) {

  def isFinished: Boolean = subGoals.isEmpty

  def currentSubGoalOption: Option[OpenAssumption] = subGoals.headOption

  def setSubGoals( newSubGoals: List[OpenAssumption] ): ProofState =
    copy( subGoals = newSubGoals )

  def focus( index: OpenAssumptionIndex ): ProofState = {
    val ( focused, rest ) = subGoals.partition( _.index == index )
    setSubGoals( focused ++ rest )
  }

  def replace( index: OpenAssumptionIndex, proofSegment: LKProof ): ProofState = {
    val subGoal = subGoals.find( _.index == index ).getOrElse(
      throw new IllegalArgumentException( s"Cannot replace non-existing open subgoal: $index" ) )
    require(
      proofSegment.conclusion isSubsetOf subGoal.conclusion,
      s"Conclusion of proof segment is not a subset of subgoal:\n${proofSegment.conclusion}\nis not a subset of\n${subGoal.conclusion}" )

    if ( subGoal == proofSegment ) return this

    val newOpenAssumptions = proofSegment.treeLike.postOrder.collect { case oa: OpenAssumption => oa }.distinct

    val subGoals_ = subGoals.filter( _.index != index ).diff( newOpenAssumptions )

    for ( ( idx, oas ) <- newOpenAssumptions.groupBy( _.index ) )
      require( oas.size == 1, s"Different new open assumptions with same index:\n${oas.mkString( "\n" )}" )
    require(
      newOpenAssumptions intersect subGoals_ isEmpty,
      s"New open assumption contains already open subgoal" )
    require(
      newOpenAssumptions.map( _.index ).toSet intersect finishedSubGoals.keySet isEmpty,
      s"New open assumption contains already finished subgoal" )

    copy(
      subGoals = newOpenAssumptions.toList ++ subGoals_,
      finishedSubGoals = finishedSubGoals + ( index -> proofSegment ) )
  }

  def replace( proofSegment: LKProof ): ProofState = replace( subGoals.head.index, proofSegment )

  class ProofSegmentInsertionVisitor( failOnMissingSubgoal: Boolean ) extends LKVisitor[Unit] {
    override def visitOpenAssumption( p: OpenAssumption, dummy: Unit ): ( LKProof, SequentConnector ) = {
      finishedSubGoals.get( p.index ) match {
        case Some( segment ) =>
          val subProof = recurse( segment, () )._1
          require( subProof.conclusion multiSetEquals segment.conclusion )
          val segment_ = WeakeningContractionMacroRule( subProof, p.conclusion )
          require( segment_.conclusion multiSetEquals p.conclusion )
          ( segment_, SequentConnector.guessInjection( segment_.conclusion, p.conclusion ).inv )
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

  def +[A]( tactical: Tactical[A] )( implicit sig: BabelSignature ): ProofState =
    tactical( this ) match {
      case Right( ( _, newState ) ) => newState
      case Left( error ) =>
        throw new TacticFailureException( s"$this\n${error.toSigRelativeString}" )
    }
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
    labelledSequent: Sequent[( String, Formula )],
    index:           OpenAssumptionIndex          = new OpenAssumptionIndex ) extends InitialSequent {
  override def name = "ass"

  def labels = labelledSequent.map( _._1 )
  override def conclusion = labelledSequent map { labelledFormula => labelledFormula._2 }

  def apply( label: String ): Formula = labelledSequent.elements.find( _._1 == label ).get._2

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

case class TacticalFailure( tactical: Tactical[_], state: Option[ProofState], message: String ) {
  def defaultState( proofState: ProofState ): TacticalFailure =
    copy( state = Some( state.getOrElse( proofState ) ) )

  override def toString = toSigRelativeString
  def toSigRelativeString( implicit sig: BabelSignature ) =
    s"$tactical: $message:\n\n${state.map( _.toSigRelativeString ).getOrElse( "" )}"
  def reassignTactical( newTactical: Tactical[_] ) =
    TacticalFailure( newTactical, state, s"$tactical: $message" )
}
object TacticalFailure {
  def apply( tactical: Tactical[_], state: ProofState, message: String ): TacticalFailure =
    TacticalFailure( tactical, Some( state ), message )
  def apply( tactical: Tactic[_], message: String ): TacticalFailure =
    TacticalFailure( tactical, None, message )
}

trait Tactical[+T] { self =>
  def apply( proofState: ProofState ): Either[TacticalFailure, ( T, ProofState )]

  /**
   * Returns result of first tactical, if there is any,
   * else it returns the result of the second tactical,
   * with the possibility of no result from either.
   *
   * @param t2
   * @return
   */
  def orElse[S >: T]( t2: => Tactical[S] ): Tactical[S] = {
    val t1 = this

    new Tactical[S] {
      override def apply( proofState: ProofState ) = {
        t1( proofState ).orElse( t2( proofState ) )
      }
      override def toString = s"$t1 orElse $t2"
    }
  }

  def andThen[S]( t2: => Tactical[S] ): Tactical[S] = new Tactical[S] {
    def apply( proofState: ProofState ) = self( proofState ) flatMap { x => t2( x._2 ) }
    override def toString = s"$self andThen $t2"
  }

  def map[S]( f: T => S )( implicit file: sourcecode.File, line: sourcecode.Line ): Tactical[S] = new Tactical[S] {
    def apply( proofState: ProofState ) = self( proofState ) map { x => f( x._1 ) -> x._2 }
    override def toString = s"$self.map(<${file.value}:${line.value}>)"
  }

  def flatMap[S]( f: T => Tactical[S] )( implicit file: sourcecode.File, line: sourcecode.Line ): Tactical[S] = new Tactical[S] {
    def apply( proofState: ProofState ) = self( proofState ) flatMap { x => f( x._1 )( x._2 ) }
    override def toString = s"$self.flatMap(<${file.value}:${line.value}>)"
  }

  private def applyToSubgoal( proofState: ProofState, subGoal: OpenAssumptionIndex, tacticToBlame: Tactical[_] = this ): Either[TacticalFailure, ( T, ProofState )] =
    proofState.subGoals.indexWhere( _.index == subGoal ) match {
      case -1 => Left( TacticalFailure( tacticToBlame, proofState, "Did not find specified subgoal" ) )
      case i =>
        val focused = proofState.subGoals( i )
        self( proofState.setSubGoals( List( focused ) ) ).flatMap {
          case ( res, newState ) =>
            Right( ( res, newState.setSubGoals( proofState.subGoals.take( i ) ++ newState.subGoals ++ proofState.subGoals.drop( i + 1 ) ) ) )
        }
    }

  def onCurrentSubGoal: Tactical[T] = new Tactical[T] {
    override def apply( proofState: ProofState ) = proofState.currentSubGoalOption match {
      case Some( goal ) =>
        self.applyToSubgoal( proofState, goal.index, this )
      case None =>
        Left( TacticalFailure( this, proofState, "No open subgoal" ) )
    }
    override def toString = s"$self.onCurrentSubGoal"
  }

  def onAllSubGoals: Tactical[Unit] = new Tactical[Unit] {
    override def apply( proofState: ProofState ): Either[TacticalFailure, ( Unit, ProofState )] =
      proofState.subGoals.foldLeft[Either[TacticalFailure, ProofState]]( Right( proofState ) )( ( proofState_, subGoal ) =>
        proofState_.flatMap( self.applyToSubgoal( _, subGoal.index, this ) ).map( _._2 ) ).map( () -> _ )

    override def toString = s"$self.onAllSubGoals"
  }

  def onAll[S]( t2: Tactical[S] ): Tactical[Unit] =
    flatMap( _ => t2.onAllSubGoals ).onCurrentSubGoal.aka( s"$this.onAll($t2)" )

  def aka( newName: => String ): Tactical[T] = new Tactical[T] {
    def apply( proofState: ProofState ) = self( proofState )
    override def toString = newName
  }

  def cut( errorMessage: String ): Tactical[T] = new Tactical[T] {
    def apply( proofState: ProofState ) =
      self( proofState ).leftMap( _ => TacticalFailure( self, proofState, errorMessage ) )
    override def toString = self.toString
  }

  def verbose: Tactical[T] = new Tactical[T] {
    override def apply( proofState: ProofState ) =
      at.logic.gapt.utils.verbose { self( proofState ) }

    override def toString: String = s"${self.toString}.verbose"
  }
}
object Tactical {
  def apply[T]( tactical: Tactical[T] )( implicit name: sourcecode.Name, args: sourcecode.Args ): Tactical[T] =
    new Tactical[T] {
      def apply( proofState: ProofState ) = tactical( proofState ).leftMap( _.reassignTactical( this ) )
      override def toString =
        if ( args.value.isEmpty ) name.value
        else s"${name.value}(${args.value.flatten.map( _.value ).mkString( ", " )})"
    }

  def sequence[T]( tacticals: Seq[Tactical[T]] ): Tactical[List[T]] = {
    tacticals.toList.sequence.aka( s"sequence(${tacticals.mkString( ", " )})" )
  }

  def sequence[T]( tacticals: Sequent[Tactical[T]] ): Tactical[Sequent[T]] =
    sequence( tacticals.elements ).map( resultElements =>
      Sequent(
        resultElements.take( tacticals.antecedent.size ),
        resultElements.drop( tacticals.antecedent.size ) ) ).aka( s"sequence($tacticals)" )

  def guard( cond: => Boolean, message: => String )( implicit args: sourcecode.Args ): Tactical[Unit] =
    new Tactical[Unit] {
      def apply( proofState: ProofState ): Either[TacticalFailure, ( Unit, ProofState )] =
        if ( cond ) Right( (), proofState )
        else Left( TacticalFailure( this, proofState, message ) )
      override def toString = s"guard(${args.value.head.head})"
    }
}

trait Tactic[+T] extends Tactical[T] { self =>
  def apply( goal: OpenAssumption ): Either[TacticalFailure, ( T, LKProof )]

  override def apply( proofState: ProofState ): Either[TacticalFailure, ( T, ProofState )] =
    proofState.currentSubGoalOption match {
      case None => Left( TacticalFailure( this, proofState, "no open subgoal" ) )
      case Some( goal ) => this( goal ) map {
        case ( res, proofSegment ) =>
          res -> proofState.replace( goal.index, proofSegment )
      } leftMap { _.defaultState( proofState ) }
    }

  protected def findFormula( goal: OpenAssumption, mode: TacticApplyMode ): FindFormula =
    new FindFormula( goal, mode )
  protected class FindFormula( goal: OpenAssumption, mode: TacticApplyMode ) {
    type Val = ( String, Formula, SequentIndex )

    def withFilter( pred: Val => Boolean ): Either[TacticalFailure, Val] =
      goal.labelledSequent.zipWithIndex.elements.collect {
        case ( ( l, f ), i ) if mode.forall { _ == l } && pred( l, f, i ) => ( l, f, i )
      } match {
        case Seq( f ) => Right( f )
        case Seq( someFormula, _* ) =>
          mode match {
            case AnyFormula => Right( someFormula )
            case _          => Left( TacticalFailure( self, s"Formula could not be uniquely determined." ) )
          }
        case _ =>
          mode match {
            case OnLabel( l ) => Left( TacticalFailure( self, s"Label $l not found." ) )
            case _            => Left( TacticalFailure( self, s"No matching formula found." ) )
          }
      }

    def flatMap[U]( func: Val => Either[TacticalFailure, U] ): Either[TacticalFailure, U] =
      withFilter( _ => true ).flatMap( func )
  }
}
object Tactic {
  def apply[T]( tactic: Tactic[T] )( implicit name: sourcecode.Name, args: sourcecode.Args ): Tactic[T] =
    new Tactic[T] {
      def apply( goal: OpenAssumption ) = tactic( goal )
      override def toString =
        if ( args.value.isEmpty ) name.value else s"$name(${args.value.mkString( ", " )})"
    }
}

/**
 * Trait for tactics that create two new subgoals. Provides the `left` and `right` methods.
 */
trait BinaryTactic[+T] extends Tactic[T] {

  /**
   * Synonym for `andThen`.
   */
  def left( that: Tactical[Unit] ): Tactical[Unit] = this andThen that

  /**
   * Creates a new Tactical by first applying `this` to the current subgoal and then `that` to the new right subgoal.
   * @param that A Tactical.
   */
  def right( that: Tactical[Unit] ): Tactical[Unit] = this andThen focus( 1 ) andThen that
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
  def apply( sequent: Sequent[( String, Formula )], fromLabel: String ): Stream[String] = {
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
  def apply( sequent: Sequent[( String, Formula )], fromLabel: String ): String =
    NewLabels( sequent, fromLabel ).head
}