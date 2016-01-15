package at.logic.gapt.proofs.lk

object quantRulesNumber {
  def apply( p: LKProof ): Int =
    p.treeLike.postOrder count {
      case StrongQuantifierRule( _, _, _, _, _ )  => true
      case WeakQuantifierRule( _, _, _, _, _, _ ) => true
      case _                                      => false
    }
}

object weakQuantRulesNumber {
  def apply( p: LKProof ): Int =
    p.treeLike.postOrder count {
      case WeakQuantifierRule( _, _, _, _, _, _ ) => true
      case _                                      => false
    }
}

object cutsNumber {
  def apply( p: LKProof ): Int =
    p.treeLike.postOrder count {
      case CutRule( _, _, _, _ ) => true
      case _                     => false
    }
}

object rulesNumber {
  def apply( p: LKProof ): Int = p.treeLike.size.toInt
}