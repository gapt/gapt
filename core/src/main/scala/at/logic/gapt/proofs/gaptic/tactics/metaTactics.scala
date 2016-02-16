package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr.{ clauseSubsumption, StillmanSubsumptionAlgorithmFOL }
import at.logic.gapt.proofs.SequentIndex
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.{ LKProof, WeakeningMacroRule }
import scalaz._
import Scalaz._

/**
 * Repeat tactical
 * Repeatedly applies the given tactical to a proof state until it fails.
 *
 * @param tact
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
 * Insert tactic
 * Inserts an LKProof if the insertion sequent subsumes the sequent of the sub goal
 *
 * @param insertion
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
