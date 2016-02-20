package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr.{ clauseSubsumption, StillmanSubsumptionAlgorithmFOL }
import at.logic.gapt.proofs.SequentIndex
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.{ LKProof, WeakeningMacroRule }
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
      case Some( sub ) =>
        ( (), WeakeningMacroRule( sub( insertion ), goal.endSequent ) ).success
      case None => TacticalFailure( this, Some( goal ), s"goal is not subsumed by ${insertion.endSequent}" ).failureNel
    }
  }
}

/**
 * Trivial "unit" tactical.
 */
case object SkipTactical extends Tactical[Unit] {
  def apply( proofState: ProofState ) = ( (), proofState ).success
}
