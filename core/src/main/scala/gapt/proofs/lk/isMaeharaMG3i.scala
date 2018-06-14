package gapt.proofs.lk

import gapt.expr.To
import gapt.proofs.SequentIndex

/**
 * Checks whether a given proof in LK is in the calculus L'J introduced in [Maehara 1954].  In
 * [Troelstra et al. 2000] this calculus is referred to as m-G3i.
 *
 * [Maehara 1954] Maehara Shoji, Eine Darstellung der intuitionistischen Logik in der klassischen, 1954.
 * [Troelstra et al. 2000] Troelstra, Schwichtenberg, Basic Proof Theory, 2000.
 */
object isMaeharaMG3i {

  def checkInference( p: LKProof ): Either[Seq[SequentIndex], Unit] =
    p match {
      // These are the restrictions listed in Maehara's paper
      case NegRightRule( q, _ ) =>
        if ( q.conclusion.succedent.isEmpty ) Right( () )
        else Left( p.conclusion.indicesSequent.succedent.dropRight( 1 ) )
      case ImpRightRule( q, _, _ ) =>
        if ( q.conclusion.succedent.size <= 1 ) Right( () )
        else Left( p.conclusion.indicesSequent.succedent.dropRight( 1 ) )
      case ForallRightRule( q, _, _, _ ) =>
        if ( q.conclusion.succedent.size <= 1 ) Right( () )
        else Left( p.conclusion.indicesSequent.succedent.dropRight( 1 ) )

      // The soundness proof is easy enough:
      // we can convert any mG3i-proof of Γ :- Δ into an LJ-proof of Γ :- ∨∆.
      // (Straightforward induction on the derivation.)

      // At first, we might assume that we need to restrict induction as well,
      // since it implicitly uses an implication-right rule.  However, we can get around
      // this by changing the induction formula: we just do induction on the formula ∨Δ instead.
      case InductionRule( _, _, t ) =>
        if ( t.ty == To ) // let's just make sure we don't do induction on props...
          Left( p.mainIndices )
        else
          Right( () )

      case _ => Right( () )
    }

  def apply( p: LKProof ): Boolean =
    p.subProofs.forall( checkInference( _ ).isRight )

}
