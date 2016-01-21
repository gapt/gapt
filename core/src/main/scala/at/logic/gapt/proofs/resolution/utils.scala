package at.logic.gapt.proofs.resolution

import at.logic.gapt.proofs.HOLClause

object numberOfResolutionsAndParamodulations {
  def apply( p: ResolutionProof ): Int =
    p.subProofs.count {
      case Resolution( _, _, _, _ )           => true
      case Paramodulation( _, _, _, _, _, _ ) => true
      case _                                  => false
    }
}

object inputClauses {
  def apply( p: ResolutionProof ): Set[HOLClause] = p.subProofs.collect { case InputClause( clause ) => clause }
}

object containsEquationalReasoning {
  def apply( p: ResolutionProof ): Boolean = p.subProofs exists {
    case _: Paramodulation    => true
    case _: ReflexivityClause => true
    case _                    => false
  }
}