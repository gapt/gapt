package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ SequentIndex, Sequent }
import at.logic.gapt.proofs.lk._
import scalaz._
import Scalaz._
import Validation.FlatMap._

/**
 * Immutable object defining the current state of the proof in the tactics language.
 *
 * @param currentGoalIndex
 * @param proofSegment
 */
case class ProofState( currentGoalIndex: Int, proofSegment: LKProof ) {
  val initSegment = proofSegment.endSequent

  val subGoals: Seq[OpenAssumption] =
    for ( OpenAssumption( s ) <- proofSegment.treeLike.postOrder )
      yield OpenAssumption( s )

  require( currentGoalIndex >= 0 && currentGoalIndex <= subGoals.length )

  /**
   *
   * Constructor with name of theorem and initial formula.
   */
  def this( proofSegment: LKProof ) = this( 0, proofSegment )

  /**
   * Returns the sub goal at a given index if it exists.
   *
   * @param i
   * @return
   */
  def getSubGoal( i: Int ): Option[OpenAssumption] =
    if ( subGoals isDefinedAt i ) Some( subGoals( i ) ) else None

  /**
   * Returns a string representation of a sub goal at a given index.
   *
   * @param i
   * @return
   */
  def displaySubGoal( i: Int ): String = {
    getSubGoal( i ) match {
      case Some( o: OpenAssumption ) => o.s.toString
      case None                      => "No sub goal found with index " + i
    }
  }

  /**
   * Returns a new proof state if the new sub goal index is valid
   *
   * @param i
   * @return
   */
  def setCurrentSubGoal( i: Int ): Option[ProofState] =
    if ( subGoals isDefinedAt i ) Some( copy( currentGoalIndex = i ) ) else None

  /**
   * Replaces the i-th open assumption by an arbitrary proof segment and returns the result in a new proof state.
   *
   * @param openAssumption
   * @param replacementSegment
   * @return
   */
  def replaceSubGoal( openAssumption: Int, replacementSegment: LKProof ): ProofState = {
    var assumptionIndex = -1

    // Replacement function - applied recursively
    def f( p: LKProof ): LKProof = p match {
      // Open assumption. Replace on matching index.
      case OpenAssumption( _ ) =>
        assumptionIndex += 1
        if ( assumptionIndex == openAssumption )
          WeakeningContractionMacroRule( replacementSegment, p.conclusion )
        else
          p
      // Case distinction on rules
      case InitialSequent( s )                                         => Axiom( s )
      case ContractionLeftRule( subProof, index1, _ )                  => ContractionLeftRule( f( subProof ), subProof.conclusion( index1 ) )
      case ContractionRightRule( subProof, index1, _ )                 => ContractionRightRule( f( subProof ), subProof.conclusion( index1 ) )
      case WeakeningLeftRule( subProof, formula )                      => WeakeningLeftRule( f( subProof ), formula )
      case WeakeningRightRule( subProof, formula )                     => WeakeningRightRule( f( subProof ), formula )
      case CutRule( leftSubProof, index1, rightSubProof, index2 )      => CutRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case NegLeftRule( subProof, index )                              => NegLeftRule( f( subProof ), subProof.conclusion( index ) )
      case NegRightRule( subProof, index )                             => NegRightRule( f( subProof ), subProof.conclusion( index ) )
      case AndLeftRule( subProof, index1, index2 )                     => AndLeftRule( f( subProof ), subProof.conclusion( index1 ), subProof.conclusion( index2 ) )
      case AndRightRule( leftSubProof, index1, rightSubProof, index2 ) => AndRightRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case OrLeftRule( leftSubProof, index1, rightSubProof, index2 )   => OrLeftRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case OrRightRule( subProof, index1, index2 )                     => OrRightRule( f( subProof ), subProof.conclusion( index1 ), subProof.conclusion( index2 ) )
      case ImpLeftRule( leftSubProof, index1, rightSubProof, index2 )  => ImpLeftRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case ImpRightRule( subProof, index1, index2 )                    => ImpRightRule( f( subProof ), subProof.conclusion( index1 ), subProof.conclusion( index2 ) )
      case ForallLeftRule( subProof, _, a, term, v )                   => ForallLeftRule( f( subProof ), All( v, a ), term )
      case ForallRightRule( subProof, index, ev, qv )                  => ForallRightRule( f( subProof ), All( qv, Substitution( ev, qv )( subProof.conclusion( index ) ) ), ev )
      case ExistsLeftRule( subProof, index, ev, qv )                   => ExistsLeftRule( f( subProof ), Ex( qv, Substitution( ev, qv )( subProof.conclusion( index ) ) ), ev )
      case ExistsRightRule( subProof, _, a, term, v )                  => ExistsRightRule( f( subProof ), Ex( v, a ), term )
      case EqualityLeftRule( subProof, eq, index, pos )                => EqualityLeftRule( f( subProof ), subProof.conclusion( eq ), subProof.conclusion( index ), pos )
      case EqualityRightRule( subProof, eq, index, pos )               => EqualityRightRule( f( subProof ), subProof.conclusion( eq ), subProof.conclusion( index ), pos )
      case DefinitionLeftRule( subProof, index, main )                 => DefinitionLeftRule( f( subProof ), subProof.conclusion( index ), main )
      case DefinitionRightRule( subProof, index, main )                => DefinitionRightRule( f( subProof ), subProof.conclusion( index ), main )
      case _ =>
        throw new Exception( "Unmatched LK rule: " + p + ". Could not replace sub goal." )
    }

    val newSegment = f( proofSegment )

    ProofState( currentGoalIndex, newSegment )
  }

  override def toString =
    s"""${subGoals.map { _.toPrettyString }.mkString( "\n" )}
     |
     |Partial proof:
     |$proofSegment
   """.stripMargin
}

/**
 * Defines the case class open assumption which considers an arbitrary labelled sequence an axiom.
 *
 * @param s
 */
case class OpenAssumption( s: Sequent[( String, HOLFormula )] ) extends InitialSequent {
  override def conclusion = s map { labelledFormula => labelledFormula._2 }

  def toPrettyString = {
    val builder = new StringBuilder
    for ( ( l, f ) <- s.antecedent ) builder append s"$l: $f\n"
    builder append ":-\n"
    for ( ( l, f ) <- s.succedent ) builder append s"$l: $f\n"
    builder.toString
  }
}

case class TacticalFailure( tactical: Tactical[_], goal: Option[OpenAssumption], message: String ) {
  override def toString = s"$tactical: $message:${goal.map( "\n" + _.toPrettyString ).getOrElse( "" )}"
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
      Applicative[StrVal].traverse( proofState.subGoals.toList )( subGoal => self.asTactic( subGoal ) ) map {
        _.zipWithIndex.foldRight( proofState ) { case ( ( subState, index ), state ) => state.replaceSubGoal( index, subState._2 ) }
      } map { x => ( (), x ) }
    }
    override def toString = s"$self.onAllSubGoals"
  }

  def asTactic: Tactic[T] = new Tactic[T] {
    def apply( goal: OpenAssumption ) = self( ProofState( 0, goal ) ) map { case ( res, p ) => res -> p.proofSegment }
    override def toString = s"$self.asTactic"
  }
}

trait Tactic[+T] extends Tactical[T] { self =>
  def apply( goal: OpenAssumption ): ValidationNel[TacticalFailure, ( T, LKProof )]

  override def apply( proofState: ProofState ): ValidationNel[TacticalFailure, ( T, ProofState )] =
    proofState getSubGoal proofState.currentGoalIndex match {
      case None => TacticalFailure( this, None, "no open subgoal" ).failureNel
      case Some( goal ) => this( goal ) map {
        case ( res, proofSegment ) =>
          res -> proofState.replaceSubGoal( proofState currentGoalIndex, proofSegment )
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

  protected def findFormula( goal: OpenAssumption, label: Option[String] ): FindFormula =
    new FindFormula( goal, label )
  protected class FindFormula( goal: OpenAssumption, label: Option[String] ) {
    type Val = ( String, HOLFormula, SequentIndex )

    def withFilter( pred: Val => Boolean ): ValidationNel[TacticalFailure, Val] =
      goal.s.zipWithIndex.elements.collect {
        case ( ( l, f ), i ) if label.forall { _ == l } && pred( l, f, i ) => ( l, f, i )
      } match {
        case Seq( someFormula, _* ) => someFormula.success
        case _ =>
          label match {
            case Some( l ) => TacticalFailure( self, Some( goal ), s"label $l not found" ).failureNel
            case _         => TacticalFailure( self, Some( goal ), s"no matching formula found" ).failureNel
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
