package gapt.proofs.lk

import gapt.expr.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent

/**
 * An LKProof ending with a right weakening:
 * <pre>
 *        (π)
 *       Γ :- Δ
 *     ---------w:r
 *     Γ :- Δ, A
 * </pre>
 *
 * @param subProof The subproof π.
 * @param formula The formula A.
 */
case class WeakeningRightRule( subProof: LKProof, formula: Formula )
  extends UnaryLKProof with CommonRule {
  override def auxIndices: Seq[Seq[Nothing]] = Seq( Seq() )
  override def name: String = "w:r"
  def mainFormula: Formula = formula

  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}
