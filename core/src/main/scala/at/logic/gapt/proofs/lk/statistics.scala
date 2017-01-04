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

object strongQuantRulesNumber {
  def apply( p: LKProof ): Int =
    p.treeLike.postOrder count {
      case StrongQuantifierRule( _, _, _, _, _ ) => true
      case _                                     => false
    }
}

object cutsNumber {
  def apply( p: LKProof ): Int =
    p.treeLike.postOrder count {
      case CutRule( _, _, _, _ ) => true
      case _                     => false
    }
}

object inductionsNumber {
  def apply( p: LKProof ): Int =
    p.treeLike.postOrder count {
      case InductionRule( _, _, _ ) => true
      case _                        => false
    }
}

object rulesNumber {
  def apply( p: LKProof ): Int = p.treeLike.size.toInt
}

object printProofStats {
  def apply( p: LKProof ): Unit =
    print(
      s"""
         |Inferences: ${rulesNumber( p )}
         |Cuts: ${cutsNumber( p )}
         |Inductions: ${inductionsNumber( p )}
         |Strong quantifier inferences: ${strongQuantRulesNumber( p )}
         |Weak quantifier inferences: ${weakQuantRulesNumber( p )}
         |Equality inferences: ${p.treeLike.postOrder.count { _.isInstanceOf[EqualityRule] }}
       """.stripMargin
    )
}
