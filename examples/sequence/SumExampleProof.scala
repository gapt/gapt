package sequence

import gapt.expr._
import gapt.expr.formula.fol.Utils
import gapt.proofs.Sequent
import gapt.proofs.gaptic.Proof
import gapt.proofs.gaptic.chain
import gapt.proofs.gaptic.prop
import gapt.proofs.gaptic.repeat
import gapt.proofs.lk.LKProof

/**
 * Functions to construct the straightforward cut-free FOL LK proofs of the sequents
 *
 * P(s^n^(0),0), ∀x,y. P(s(x),y) → P(x,s(y)) :- P(0,s^n^(0))
 *
 * where n is an Integer parameter >= 0.
 *
 * This sequent is shown to have no cut-free proof which can be compressed by a
 * single cut with a single quantifier in S. Eberhard, S. Hetzl: On the
 * compressibility of finite languages and formal proofs, submitted, 2015.
 */
object SumExampleProof extends ProofSequence {

  /**
   * @param n An integer >= 0.
   * @return A proof of P(s^n^(0),0), ∀x,y. P(s(x),y) → P(x,s(y)) :- P(0,s^n^(0))
   */
  def apply( n: Int ): LKProof = {
    require( n >= 0, "n must be nonnegative" )

    val num = Utils.numeral( n )
    val pn0 = foa"P($num,0)"
    val p0n = foa"P(0,$num)"
    val ax = fof" ∀x ∀y (P(s(x),y) -> P(x, s(y)))"

    Proof( Sequent( Seq( "Pn0" -> pn0, "Ax" -> ax ), Seq( "P0n" -> p0n ) ) ) {
      repeat( chain( "Ax" ) )
      prop
    }
  }
}
