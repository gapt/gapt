package gapt.examples.sequence

import gapt.expr._
import gapt.expr.formula.fol.Utils
import gapt.proofs.Sequent
import gapt.proofs.gaptic.Proof
import gapt.proofs.gaptic.chain
import gapt.proofs.gaptic.prop
import gapt.proofs.gaptic.repeat
import gapt.proofs.lk.LKProof

/**
 * Constructs cut-free FOL LK proofs of the sequents
 *
 * P(0), ∀x. P(x) → P(s(x)) :- P(s^n^(0))
 *
 * where n is an Integer parameter >= 0.
 */
object LinearExampleProof extends ProofSequence {

  /**
   * @param n An integer >= 0.
   * @return A proof of P(0), ∀x. P(x) → P(s(x)) :- P(s^n^(0))
   */
  def apply(n: Int): LKProof = {
    require(n >= 0, "n must be nonnegative")

    val num = Utils.numeral(n)
    val ax = fof"!x (P x -> P (s x))"
    val p0 = foa"P(0)"
    val pn = foa"P($num)"
    Proof(Sequent(Seq("P0" -> p0, "Ax" -> ax), Seq("Pn" -> pn))) {
      repeat(chain("Ax"))
      prop
    }
  }
}
