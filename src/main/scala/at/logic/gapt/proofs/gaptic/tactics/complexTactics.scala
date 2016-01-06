package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.proofs.gaptic.{ ProofState, Tactical }

/**
 * Created by Alexander on 06-01-2016.
 */
case object DecomposeTactic extends Tactical {
  def apply( proofState: ProofState ) = {
    RepeatTactic(
      AndLeftTactic()
        orElse OrRightTactic()
        orElse ImpRightTactic()
        orElse ForallRightTactic()
        orElse ExistsLeftTactic()
    )( proofState )
  }
}
