package gapt.proofs.lk.rules

import gapt.expr.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a left weakening:
 * <pre>
 *        (π)
 *       Γ :- Δ
 *     ---------w:l
 *     A, Γ :- Δ
 * </pre>
 *
 * @param subProof The subproof π.
 * @param formula The formula A.
 */
case class WeakeningLeftRule( subProof: LKProof, formula: Formula )
  extends UnaryLKProof with CommonRule {
  override def auxIndices: Seq[Seq[Nothing]] = Seq( Seq() )
  override def name: String = "w:l"
  def mainFormula: Formula = formula

  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}
