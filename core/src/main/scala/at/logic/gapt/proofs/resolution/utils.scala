package at.logic.gapt.proofs.resolution

object numberOfLogicalInferencesRes {
  def apply( p: ResolutionProof ): Int =
    p.subProofs.count {
      case Resolution( _, _, _, _ )           => true
      case Paramodulation( _, _, _, _, _, _ ) => true
      case Splitting( _, _, _, _ )            => true
      case _                                  => false
    }
}

object containsEquationalReasoning {
  def apply( p: ResolutionProof ): Boolean = p.subProofs exists {
    case _: Paramodulation    => true
    case _: ReflexivityClause => true
    case _                    => false
  }
}