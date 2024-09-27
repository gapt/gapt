package gapt.examples.sequence

import gapt.expr._
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.Utils
import gapt.proofs.Sequent
import gapt.proofs.gaptic.Proof
import gapt.proofs.gaptic.chain
import gapt.proofs.gaptic.prop
import gapt.proofs.gaptic.repeat
import gapt.proofs.lk.LKProof

/**
 * Functions to construct cut-free FOL LK proofs of the sequents
 *
 * P(a,b), ∀x,y. P(x,y) → P(s,,x,,(x),y), ∀x,y. P(x,y) → P(x,s,,y,,(y)) :- P(s,,x,,^n^(a),s,,y,,^n^(b))
 *
 * where n is an Integer parameter >= 0.
 *
 * The proofs constructed here go along the edges of P, i.e. first all X-steps are performed,
 * then all Y-steps are performed,
 * but unlike SquareEdgesExampleProof, different functions are used for the X- and the Y-directions.
 */
object SquareEdges2DimExampleProof extends ProofSequence {

  /**
   * @param n An integer >= 0.
   * @return P(a,b), ∀x,y. P(x,y) → P(s,,x,,(x),y), ∀x,y. P(x,y) → P(x,s,,y,,(y)) :- P(s,,x,,^n^(a),s,,y,,^n^(b))
   */
  def apply(n: Int): LKProof = {
    require(n >= 0, "n must be nonnegative")

    val sna = Utils.iterateTerm(FOLConst("a"), "s_x", n)
    val snb = Utils.iterateTerm(FOLConst("b"), "s_y", n)
    val pab = foa"P(a,b)"
    val pnn = foa"P($sna, $snb)"
    val axX = fof"!x!y (P(x,y) -> P(s_x(x), y))"
    val axY = fof"!x!y (P(x,y) -> P(x, s_y(y)))"

    Proof(Sequent(Seq("Pab" -> pab, "AxX" -> axX, "AxY" -> axY), Seq("Pnn" -> pnn))) {
      repeat(chain("AxY"))
      repeat(chain("AxX"))
      prop
    }
  }
}
