package at.logic.gapt.proofs.lk

/**
 * Checks whether a given proof in LK is in the calculus L'J introduced in [Maehara 1954].  In
 * [Troelstra et al. 2000] this calculus is referred to as m-G3i.
 *
 * [Maehara 1954] Maehara Shoji, Eine Darstellung der intuitionistischen Logik in der klassischen, 1954.
 * [Troelstra et al. 2000] Troelstra, Schwichtenberg, Basic Proof Theory, 2000.
 */
object isMaeharaMG3i {
  def apply( p: LKProof ): Boolean = p.subProofs.forall {
    // These are the restrictions listed in Maehara's paper
    case NegRightRule( q, _ )          => q.conclusion.succedent.isEmpty
    case ImpRightRule( q, _, _ )       => q.conclusion.succedent.size <= 1
    case ForallRightRule( q, _, _, _ ) => q.conclusion.succedent.size <= 1

    // The soundness proof is easy enough:
    // we can convert any mG3i-proof of Γ :- Δ into an LJ-proof of Γ :- ∨∆.
    // (Straightforward induction on the derivation.)

    // At first, we might assume that we need to restrict induction as well,
    // since it implicitly uses an implication-right rule.  However, we can get around
    // this by changing the induction formula: we just do induction on the formula ∨Δ instead.
    case InductionRule( _, _, _ )      => true

    case _                             => true
  }
}
