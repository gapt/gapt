package gapt.proofs.gaptic.tactics

import gapt.expr.clauseSubsumption
import gapt.proofs.gaptic._
import gapt.proofs.lk._

/**
 * Applies the given [[Tactic]] to the proof state until it fails.
 *
 * Note that the tactical is not required to succeed at least once, i.e. it might
 * fail immediately.
 *
 * @param tact The [[Tactic]] to be repeated.
 */
case class RepeatTactic[T]( tact: Tactic[T] ) extends Tactic[Unit] {
  def apply( proofState: ProofState ): Either[TacticFailure, ( Unit, ProofState )] =
    tact( proofState ) match {
      case Right( ( _, newState ) ) => apply( newState )
      case Left( _ )                => Right( (), proofState )
    }
}

/**
 * Inserts an [[gapt.proofs.lk.LKProof]] if the insertion sequent subsumes the sequent of the subgoal.
 *
 * @param insertion The [[gapt.proofs.lk.LKProof]] to be inserted. Its end sequent must subsume the current goal.
 */
case class InsertTactic( insertion: LKProof ) extends Tactical1[Unit] {
  def apply( goal: OpenAssumption ) = {
    if ( insertion.endSequent.isSubsetOf( goal.endSequent ) ) replace( insertion )
    else clauseSubsumption( insertion.endSequent, goal.endSequent ) match {
      case Some( sub ) =>
        replace( sub( insertion ) )
      case None =>
        TacticFailure( this, "goal is not subsumed by provided proof" )
    }
  }

  override def toString = s"insert(${insertion.conclusion})"
}

case class RenameTactic( oldLabel: String, newLabel: String ) extends Tactical1[Unit] {
  def apply( goal: OpenAssumption ) =
    goal.labelledSequent.find( _._1 == oldLabel ) match {
      case Some( idx ) =>
        replace( OpenAssumption( goal.labelledSequent.updated( idx, newLabel -> goal.conclusion( idx ) ) ) )
      case None => TacticFailure( this, s"Old label $oldLabel not found" )
    }

  def to( newLabel: String ) = copy( newLabel = newLabel )
}

case class FocusTactic( index: Either[Int, OpenAssumptionIndex] ) extends Tactic[Unit] {
  def apply( proofState: ProofState ) =
    index match {
      case Left( i ) if 0 <= i && i < proofState.subGoals.size =>
        Right( () -> proofState.focus( proofState.subGoals( i ).index ) )
      case Right( i ) => Right( () -> proofState.focus( i ) )
      case _          => Left( TacticFailure( this, proofState, s"Cannot find subgoal $index" ) )
    }
}
