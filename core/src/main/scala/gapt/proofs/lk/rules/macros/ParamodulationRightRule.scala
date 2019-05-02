package gapt.proofs.lk.rules.macros

import gapt.expr.Abs
import gapt.expr.formula.Formula
import gapt.proofs.Ant
import gapt.proofs.IndexOrFormula
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ConvenienceConstructor
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.WeakeningLeftRule

object ParamodulationRightRule extends ConvenienceConstructor( "ParamodulationLeftRule" ) {

  /**
   * Simulates a binary equation rule, aka paramodulation.
   *
   * A binary rule of the form
   * <pre>
   *        (π1)              (π2)
   *     Γ,Δ :- s = t   Π :- Λ, A[s]
   *   ------------------------------par:r
   *         Γ, Π :- Δ, Λ, A[t]
   * </pre>
   * is expressed as a series of inferences:
   * <pre>
   *                               (π2)
   *                         Π :- Λ, A[s]
   *                     --------------------w:l
   *                     s = t, Π :- Λ, A[s]
   *       (π1)         ---------------------:eq:r
   *   Γ, Δ :- s = t     s = t, Π :- Λ, A[t]
   *   -------------------------------------cut
   *            Γ, Π :- Δ, Λ, A[t]
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
   * @param con The positions of the term to be replaced within A.
   * @return
   */
  def apply(
    leftSubProof:  LKProof,
    eq:            IndexOrFormula,
    rightSubProof: LKProof,
    aux:           IndexOrFormula,
    con:           Abs ): LKProof = {

    val eqFormula = eq.getFormula( leftSubProof.endSequent )

    val p1 = WeakeningLeftRule( rightSubProof, eqFormula )
    val p2 = EqualityRightRule( p1, Ant( 0 ), aux, con )

    CutRule( leftSubProof, eq, p2, p2.getSequentConnector.child( Ant( 0 ) ) )
  }

  /**
   * Simulates a binary equation rule, aka paramodulation.
   *
   * A binary rule of the form
   * <pre>
   *        (π1)              (π2)
   *     Γ,Δ :- s = t   Π :- Λ, A[s]
   *   ------------------------------par:r
   *         Γ, Π :- Δ, Λ, A[t]
   * </pre>
   * is expressed as a series of inferences:
   * <pre>
   *                               (π2)
   *                         Π :- Λ, A[s]
   *                     --------------------w:l
   *                     s = t, Π :- Λ, A[s]
   *       (π1)         ---------------------:eq:r
   *   Γ, Δ :- s = t     s = t, Π :- Λ, A[t]
   *   -------------------------------------cut
   *            Γ, Π :- Δ, Λ, A[t]
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
    leftSubProof:  LKProof,
    eq:            IndexOrFormula,
    rightSubProof: LKProof,
    aux:           IndexOrFormula,
    mainFormula:   Formula ): LKProof = {

    val eqFormula = eq.getFormula( leftSubProof.endSequent )

    val p1 = WeakeningLeftRule( rightSubProof, eqFormula )
    val p2 = EqualityRightRule( p1, Ant( 0 ), aux, mainFormula )

    CutRule( leftSubProof, eq, p2, p2.getSequentConnector.child( Ant( 0 ) ) )
  }
}
