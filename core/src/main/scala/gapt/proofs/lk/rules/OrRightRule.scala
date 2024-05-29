package gapt.proofs.lk.rules

import gapt.expr.formula.Formula
import gapt.expr.formula.Or
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a disjunction on the right:
 * <pre>
 *         (π)
 *     Γ :- Δ, A, B
 *    --------------
 *     Γ :- Δ, A ∨ B
 * </pre>
 *
 * @param subProof The subproof π.
 * @param aux1 The index of A.
 * @param aux2 The index of B.
 */
case class OrRightRule(subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex)
    extends UnaryLKProof with CommonRule {

  validateIndices(premise, Seq(), Seq(aux1, aux2))

  val leftDisjunct: Formula = premise(aux1)
  val rightDisjunct: Formula = premise(aux2)
  val mainFormula: Formula = Or(leftDisjunct, rightDisjunct)

  override def auxIndices: Seq[Seq[SequentIndex]] = Seq(Seq(aux1, aux2))

  override def name: String = "∨:r"

  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}

object OrRightRule extends ConvenienceConstructor("OrRightRule") {

  /**
   * Convenience constructor for ∨:r.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param leftDisjunct Index of the left disjunct or the disjunct itself.
   * @param rightDisjunct Index of the right disjunct or the disjunct itself.
   * @return
   */
  def apply(subProof: LKProof, leftDisjunct: IndexOrFormula, rightDisjunct: IndexOrFormula): OrRightRule = {
    val premise = subProof.endSequent

    val (_, indices) = findAndValidate(premise)(Seq(), Seq(leftDisjunct, rightDisjunct))

    new OrRightRule(subProof, Suc(indices(0)), Suc(indices(1)))
  }

  /**
   * Convenience constructor for ∨:r that, given a proposed main formula A ∨ B,
   * will attempt to create an inference with this main formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A ∨ B.
   * @return
   */
  def apply(subProof: LKProof, mainFormula: Formula): OrRightRule = mainFormula match {
    case Or(f, g) =>
      val p = apply(subProof, f, g)
      assert(p.mainFormula == mainFormula)
      p
    case _ => throw LKRuleCreationException(s"Proposed main formula $mainFormula is not a disjunction.")
  }
}
