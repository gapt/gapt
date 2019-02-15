package gapt.proofs.lk.rules

import gapt.expr.formula.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.lk.LKProof

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
