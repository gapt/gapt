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
 * Functions to construct cut-free FOL LK proofs of the sequents
 *
 * P(0,0), ∀x,y. P(x,y) → P(s(x),y), ∀x,y. P(x,y) → P(x,s(y)) :- P(s^n^(0),s^n^(0))
 *
 * where n is an Integer parameter >= 0.
 *
 * The proofs constructed here go along the diagonal of P, i.e. one x-step, then one y-step, etc.
 */
object SquareDiagonalExampleProof extends ProofSequence {

  /**
   * @param n An integer >= 0.
   * @return A proof of P(0,0), ∀x,y. P(x,y) → P(s(x),y), ∀x,y. P(x,y) → P(x,s(y)) :- P(s^n^(0),s^n^(0))
   */
  def apply( n: Int ): LKProof = {
    require( n >= 0, "n must be nonnegative" )

    val num = Utils.numeral( n )
    val p00 = foa"P(0,0)"
    val pnn = foa"P($num, $num)"
    val axX = fof"!x!y (P(x,y) -> P(s(x), y))"
    val axY = fof"!x!y (P(x,y) -> P(x, s(y)))"

    Proof( Sequent( Seq( "P00" -> p00, "AxX" -> axX, "AxY" -> axY ), Seq( "Pnn" -> pnn ) ) ) {
      repeat( chain( "AxY" ) andThen chain( "AxX" ) )
      prop
    }
  }
}
