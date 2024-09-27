package gapt.proofs.lk.rules

import gapt.expr.formula.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a conversion on the right.
 *
 * <pre>
 *       (π)
 *    Γ :- Δ, M
 *   -----------conv:r
 *    Γ :- Δ, N
 * </pre>
 *
 * LK proofs that contain this rule are not sound by construction, since it allows you to replace any formula
 * by any other formula. The soundness of such proofs can only be established with respect to a context in which we have
 * M =βδ N. Use the `check` method on [[gapt.proofs.context.Context]] to check whether the constructed proof is sound.
 *
 * @param subProof The proof π.
 * @param aux The index of M in the succedent.
 * @param mainFormula The formula N.
 */
case class ConversionRightRule(subProof: LKProof, aux: SequentIndex, mainFormula: Formula) extends ConversionRule {
  override def name: String = "conv:r"
  override def auxIndices: Seq[Seq[SequentIndex]] = Seq(Seq(aux))
  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}

object ConversionRightRule extends ConvenienceConstructor("ConversionRightRule") {

  /**
   * Constructs a derivation ending in a conversion right rule.
   *
   * Constructs a derivation of the form:
   *
   * <pre>
   *        (π)
   *    Γ :- Δ, M
   *   -----------conv:r
   *    Γ :- Δ, N.
   * </pre>
   *
   * @param subProof The subproof π.
   * @param aux The auxiliary formula M or its index in the succedent.
   * @param mainFormula The main formula N.
   */
  def apply(subProof: LKProof, aux: IndexOrFormula, mainFormula: Formula): ConversionRightRule = {
    val premise = subProof.endSequent
    val (_, indices) = findAndValidate(premise)(Seq(), Seq(aux))

    ConversionRightRule(subProof, Suc(indices(0)), mainFormula)
  }
}
