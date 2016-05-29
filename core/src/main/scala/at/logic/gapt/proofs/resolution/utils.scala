package at.logic.gapt.proofs.resolution

object numberOfLogicalInferencesRes {
  def apply( p: ResolutionProof ): Int =
    p.subProofs.count {
      case Resolution( _, _, _, _ )    => true
      case Paramod( _, _, _, _, _, _ ) => true
      case _                           => false
    }
}

object containsEquationalReasoning {
  def apply( p: ResolutionProof ): Boolean = p.subProofs exists {
    case _: Paramod => true
    case _: Refl    => true
    case _          => false
  }
}