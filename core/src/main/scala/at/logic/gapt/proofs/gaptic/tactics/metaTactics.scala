package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr.StillmanSubsumptionAlgorithmFOL
import at.logic.gapt.proofs.gaptic.{ ProofState, Tactical }
import at.logic.gapt.proofs.lk.{ WeakeningMacroRule, LKProof }

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
 * Insert tactical
 * Inserts an LKProof where the end sequent subsumes the sequent of the open assumption
 * @param insertion
 */
case class InsertTactic( insertion: LKProof ) extends Tactical {
  def apply( proofState: ProofState ) = {
    var insertedOnce = false

    def f( x: ProofState, i: Int ): ProofState = x.getSubGoal( i ) match {
      case None => x
      case Some( goal ) =>
        StillmanSubsumptionAlgorithmFOL.subsumes_by( insertion.endSequent, goal.conclusion ) match {
          case None => f( x, i - 1 )
          case Some( sub ) =>
            insertedOnce = true
            val insertionContracted = WeakeningMacroRule( sub( insertion ), goal.conclusion )
            f( x replaceSubGoal ( i, insertionContracted ), i - 1 )
        }
    }

    val r = f( proofState, proofState.subGoals.length - 1 )

    if ( insertedOnce )
      Some( r )
    else
      None
  }

}
