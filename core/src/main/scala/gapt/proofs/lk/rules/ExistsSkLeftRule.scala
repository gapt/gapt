package gapt.proofs.lk.rules

import gapt.expr.Apps
import gapt.expr.BetaReduction
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.instantiate
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.context.Context
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with an existential quantifier on the left:
 * <pre>
 *           (π)
 *      A[x\s(...)], Γ :- Δ
 *     --------------- ∃sk:l
 *       ∃x.A Γ :- Δ
 * </pre>
 * This rule requires a Skolem function s(...)
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\s(...)].
 * @param mainFormula The main formula A[x\s(...)]
 * @param skolemTerm The Skolem term s(...)
 */
case class ExistsSkLeftRule(subProof: LKProof, aux: SequentIndex, mainFormula: Formula, skolemTerm: Expr)
    extends SkolemQuantifierRule {

  validateIndices(premise, Seq(aux), Seq())

  val Ex(quantifiedVariable, subFormula) = mainFormula: @unchecked

  override def name: String = "∃sk:l"

  def auxIndices: Seq[Seq[SequentIndex]] = Seq(Seq(aux))

  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}

object ExistsSkLeftRule extends ConvenienceConstructor("ExistsSkLeftRule") {

  /**
   * Convenience constructor for ∃sk:l that, given a Skolem term and Skolem definition,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @return
   */
  def apply(subProof: LKProof, skolemTerm: Expr, skolemDef: Expr): ExistsSkLeftRule = {
    val Apps(_, skolemArgs) = skolemTerm
    val mainFormula = BetaReduction.betaNormalize(skolemDef(skolemArgs: _*)).asInstanceOf[Formula]
    apply(subProof, mainFormula, skolemTerm)
  }

  def apply(subProof: LKProof, mainFormula: Formula, skolemTerm: Expr): ExistsSkLeftRule = {
    val auxFormula = instantiate(mainFormula, skolemTerm)
    val premise = subProof.endSequent
    val (indices, _) = findAndValidate(premise)(Seq(auxFormula), Seq())
    ExistsSkLeftRule(subProof, Ant(indices(0)), mainFormula, skolemTerm)
  }

  def apply(subProof: LKProof, skolemTerm: Expr)(implicit ctx: Context): ExistsSkLeftRule = {
    val Apps(skC: Const, _) = skolemTerm: @unchecked
    val skD = ctx.skolemDef(skC).getOrElse(
      throw new IllegalArgumentException(s"not a defined Skolem function: $skC")
    )
    apply(subProof, skolemTerm, skD)
  }
}
