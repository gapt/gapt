package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr.clauseSubsumption
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk._
import scalaz._
import Scalaz._

/**
 * Applies the given [[Tactical]] to the proof state until it fails.
 *
 * Note that the tactical is not required to succeed at least once, i.e. it might
 * fail immediately.
 *
 * @param tact The [[Tactical]] to be repeated.
 */
case class RepeatTactic[T]( tact: Tactical[T] ) extends Tactical[Unit] {
  override def apply( proofState: ProofState ) = {
    tact( proofState ) match {
      case Right( ( _, newState ) ) => apply( newState )
      case Left( _ )                => Right( (), proofState )
    }
  }
}

/**
 * Inserts an [[at.logic.gapt.proofs.lk.LKProof]] if the insertion sequent subsumes the sequent of the subgoal.
 *
 * @param insertion The [[at.logic.gapt.proofs.lk.LKProof]] to be inserted. Its end sequent must subsume the current goal.
 */
case class InsertTactic( insertion: LKProof ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) = {
    clauseSubsumption( insertion.endSequent, goal.endSequent ) match {
      case Some( sub ) if sub.isIdentity =>
        Right( () -> insertion )
      case Some( sub ) =>
        Right( (), sub( insertion ) )
      case None =>
        Left( TacticalFailure( this, "goal is not subsumed by provided proof" ) )
    }
  }

  override def toString = s"insert(${insertion.conclusion})"
}

case class RenameTactic( oldLabel: String, newLabel: String ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    goal.labelledSequent.find( _._1 == oldLabel ) match {
      case Some( idx ) =>
        Right( () -> OpenAssumption( goal.labelledSequent.updated( idx, newLabel -> goal.conclusion( idx ) ) ) )
      case None => Left( TacticalFailure( this, s"Old label $oldLabel not found" ) )
    }

  def to( newLabel: String ) = copy( newLabel = newLabel )
}

case class FocusTactical( index: Either[Int, OpenAssumptionIndex] ) extends Tactical[Unit] {
  def apply( proofState: ProofState ) =
    index match {
      case Left( i ) if 0 <= i && i < proofState.subGoals.size =>
        Right( () -> proofState.focus( proofState.subGoals( i ).index ) )
      case Right( i ) => Right( () -> proofState.focus( i ) )
      case _          => Left( TacticalFailure( this, proofState, s"Cannot find subgoal $index" ) )
    }
}
