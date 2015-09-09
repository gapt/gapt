package at.logic.gapt.proofs.resolution

import at.logic.gapt.proofs.resolutionOld.robinson

object numberOfResolutionsAndParamodulations {
  def apply( p: robinson.RobinsonResolutionProof ): Int =
    p.nodes.count {
      case robinson.Resolution( _ )     => true
      case robinson.Paramodulation( _ ) => true
      case _                            => false
    }
}