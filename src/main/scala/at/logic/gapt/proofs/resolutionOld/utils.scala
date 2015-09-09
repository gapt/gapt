package at.logic.gapt.proofs.resolutionOld

import at.logic.gapt.proofs.resolutionOld.robinson.{ Paramodulation, Resolution, RobinsonResolutionProof }

object numberOfResolutionsAndParamodulations {
  def apply( p: RobinsonResolutionProof ): Int =
    p.nodes.count {
      case Resolution( _ )     => true
      case Paramodulation( _ ) => true
      case _                   => false
    }
}