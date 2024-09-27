package gapt.proofs.lk.rules.macros

import gapt.expr.Abs
import gapt.expr.formula.Formula
import gapt.proofs.Ant
import gapt.proofs.IndexOrFormula
import gapt.proofs.IndexOrFormula.IsFormula
import gapt.proofs.IndexOrFormula.IsIndex
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ConvenienceConstructor
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.WeakeningLeftRule

object ParamodulationLeftRule extends ConvenienceConstructor("ParamodulationLeftRule") {

  /**
   * Simulates a binary equation rule, aka paramodulation.
   *
   * A binary rule of the form
   * <pre>
   *        (π1)              (π2)
   *     Γ,Δ :- s = t   A[s], Π :- Λ
   *   ------------------------------par:l
   *         A[t], Γ, Π :- Δ, Λ
   * </pre>
   * is expressed as a series of inferences:
   * <pre>
   *                               (π2)
   *                         A[s], Π :- Λ
   *                     --------------------w:l
   *                     s = t, A[s], Π :- Λ
   *       (π1)         ---------------------:eq:l
   *   Γ, Δ :- s = t     A[t], s = t, Π :- Λ
   *   -------------------------------------cut
   *            A[t], Γ, Π :- Δ, Λ
   * </pre>
   *
   *
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The left subproof π1.
   * @param eq The index of the equation or the equation itself.
   * @param rightSubProof The right subproof π2.
   * @param aux The index of the aux formula or the aux formula itself.
   * @return
   */
  def apply(
      leftSubProof: LKProof,
      eq: IndexOrFormula,
      rightSubProof: LKProof,
      aux: IndexOrFormula,
      con: Abs
  ): LKProof = {

    val eqFormula = eq.getFormula(leftSubProof.endSequent)

    val p1 = WeakeningLeftRule(rightSubProof, eqFormula)
    val p2 = aux match {
      case IsIndex(i) =>
        EqualityLeftRule(p1, Ant(0), i + 1, con)

      case IsFormula(f) =>
        EqualityLeftRule(p1, Ant(0), f, con)
    }

    CutRule(leftSubProof, eq, p2, p2.getSequentConnector.child(Ant(0)))
  }

  /**
   * Simulates a binary equation rule, aka paramodulation.
   *
   * A binary rule of the form
   * <pre>
   *        (π1)              (π2)
   *     Γ,Δ :- s = t   A[s], Π :- Λ
   *   ------------------------------par:l
   *         A[t], Γ, Π :- Δ, Λ
   * </pre>
   * is expressed as a series of inferences:
   * <pre>
   *                               (π2)
   *                         A[s], Π :- Λ
   *                     --------------------w:l
   *                     s = t, A[s], Π :- Λ
   *       (π1)         ---------------------:eq:l
   *   Γ, Δ :- s = t     A[t], s = t, Π :- Λ
   *   -------------------------------------cut
   *            A[t], Γ, Π :- Δ, Λ
   * </pre>
   *
   *
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The left subproof π1.
   * @param eq The index of the equation or the equation itself.
   * @param rightSubProof The right subproof π2.
   * @param aux The index of the aux formula or the aux formula itself.
   * @param mainFormula The proposed main formula.
   * @return
   */
  def apply(
      leftSubProof: LKProof,
      eq: IndexOrFormula,
      rightSubProof: LKProof,
      aux: IndexOrFormula,
      mainFormula: Formula
  ): LKProof = {

    val eqFormula = eq.getFormula(leftSubProof.endSequent)

    val p1 = WeakeningLeftRule(rightSubProof, eqFormula)
    val p2 = aux match {
      case IsIndex(i) =>
        EqualityLeftRule(p1, Ant(0), i + 1, mainFormula)

      case IsFormula(f) =>
        EqualityLeftRule(p1, Ant(0), f, mainFormula)
    }

    CutRule(leftSubProof, eq, p2, p2.getSequentConnector.child(Ant(0)))
  }
}
