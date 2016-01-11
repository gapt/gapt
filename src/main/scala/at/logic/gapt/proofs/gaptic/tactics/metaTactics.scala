package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.proofs.gaptic.{ ProofState, Tactical }

case class RepeatTactic( tact: Tactical ) extends Tactical {
  def apply( proofState: ProofState ) = {
    tact( proofState ) match {
      case Some( newState ) => apply( newState )
      case None             => Some( proofState )
    }
  }
}
