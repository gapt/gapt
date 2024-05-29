package gapt.proofs.lk.rules

import gapt.expr.formula.Formula
import gapt.expr.formula.Neg
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a negation on the right:Index of the left cut formula or the formula itself.
 * <pre>
 *       (π)
 *    A, Γ :- Δ
 *   -----------¬:r
 *   Γ :- Δ, ¬A
 * </pre>
 *
 * @param subProof The proof π.
 * @param aux The index of A in the antecedent.
 */
case class NegRightRule(subProof: LKProof, aux: SequentIndex)
    extends UnaryLKProof with CommonRule {

  validateIndices(premise, Seq(aux), Seq())

  def auxFormula: Formula = premise(aux)
  val mainFormula: Formula = Neg(auxFormula)

  override def auxIndices: Seq[Seq[SequentIndex]] = Seq(Seq(aux))
  override def name: String = "¬:r"

  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}

object NegRightRule extends ConvenienceConstructor("NegRightRule") {

  /**
   * Convenience constructor that automatically uses the first occurrence of supplied aux formula.
   *
   * @param subProof The subproof.
   * @param auxFormula The formula to be negated.
   * @return
   */
  def apply(subProof: LKProof, auxFormula: Formula): NegRightRule = {
    val premise = subProof.endSequent

    val (indices, _) = findAndValidate(premise)(Seq(auxFormula), Seq())

    new NegRightRule(subProof, Ant(indices(0)))
  }
}
