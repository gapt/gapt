package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.proofs.gaptic.{ ProofState, Tactical }

case class RepeatTactic( tact: Tactical ) extends Tactical {
  def apply( proofState: ProofState ) = {
    var stop = false

    var currentState = proofState
    var newState: Option[ProofState] = None

    while ( !stop ) {
      newState = tact( currentState )

      // Prevent further iterations or prepare for next iteration
      newState match {
        case None =>
          stop = true
        case Some( x ) =>
          currentState = x
      }
    }

    Option( currentState )
  }
}
