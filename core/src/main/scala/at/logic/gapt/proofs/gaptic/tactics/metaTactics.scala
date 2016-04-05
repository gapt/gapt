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
      case Success( ( res, newState ) ) => apply( newState )
      case Failure( _ )                 => ( (), proofState ).success
    }
  }
}

/**
 * Inserts an [[LKProof]] if the insertion sequent subsumes the sequent of the subgoal.
 *
 * @param insertion The [[LKProof]] to be inserted. Its end sequent must subsume the current goal.
 */
case class InsertTactic( insertion: LKProof ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) = {
    clauseSubsumption( insertion.endSequent, goal.endSequent ) match {
      case Some( sub ) if sub.isIdentity =>
        ( () -> insertion ).success
      case Some( sub ) =>
        ( (), sub( insertion ) ).success
      case None =>
        TacticalFailure( this, Some( goal ), s"goal is not subsumed by provided proof" ).failureNel
    }
  }

  override def toString = s"insert(${insertion.conclusion})"
}

/**
 * Trivial "unit" tactical.
 */
case object SkipTactical extends Tactical[Unit] {
  def apply( proofState: ProofState ) = ( (), proofState ).success
}

case class FocusTactical( index: Either[Int, OpenAssumptionIndex] ) extends Tactical[Unit] {
  def apply( proofState: ProofState ) =
    index match {
      case Left( i ) if 0 <= i && i < proofState.subGoals.size =>
        ( (), proofState.focus( proofState.subGoals( i ).index ) ).success
      case Right( i ) => ( (), proofState.focus( i ) ).success
      case _          => TacticalFailure( this, None, s"Cannot find subgoal $index" ).failureNel
    }
}
