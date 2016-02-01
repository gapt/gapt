package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr.StillmanSubsumptionAlgorithmFOL
import at.logic.gapt.proofs.SequentIndex
import at.logic.gapt.proofs.gaptic.{ OpenAssumption, ProofState, Tactic, Tactical }
import at.logic.gapt.proofs.lk.{ LKProof, WeakeningMacroRule }

/**
 * Repeat tactical
 * Repeatedly applies the given tactical to a proof state until it fails.
 * @param tact
 */
case class RepeatTactic( tact: Tactical ) extends Tactical {
  def apply( proofState: ProofState ) = {
    tact( proofState ) match {
      case Some( newState ) => apply( newState )
      case None             => Some( proofState )
    }
  }
}

/**
 * Insert tactic
 * Inserts an LKProof if the insertion sequent subsumes the sequent of the sub goal
 * @param insertion
 */
case class InsertTactic( insertion: LKProof ) extends Tactic {
  def apply( goal: OpenAssumption ) = {
    StillmanSubsumptionAlgorithmFOL.subsumes_by( insertion.endSequent, goal.endSequent ) match {
      case Some( sub ) =>
        Option( WeakeningMacroRule( sub( insertion ), goal.endSequent ) )
      case None => None
    }
  }
}

/**
 * Trivial "unit" tactical.
 */
object SkipTactical extends Tactical {
  def apply( proofState: ProofState ): Option[ProofState] = Some( proofState )
}
