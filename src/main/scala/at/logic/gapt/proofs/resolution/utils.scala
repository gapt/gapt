package at.logic.gapt.proofs.resolution

import at.logic.gapt.proofs.FOLClause

object numberOfResolutionsAndParamodulations {
  def apply( p: ResolutionProof ): Int =
    p.subProofs.count {
      case Resolution( _, _, _, _ )           => true
      case Paramodulation( _, _, _, _, _, _ ) => true
      case _                                  => false
    }
}

object inputClauses {
  def apply( p: ResolutionProof ): Set[FOLClause] = p.subProofs.collect { case InputClause( clause ) => clause }
}