package gapt.proofs.lk.rules.macros

import gapt.expr.formula.Formula
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.WeakeningLeftRule

/**
 * This macro rule simulates a series of weakenings in the antecedent.
 *
 */
object WeakeningLeftMacroRule {

  /**
   *
   * @param p A proof.
   * @param formulas A list of formulas.
   * @return A new proof whose antecedent contains new occurrences of the formulas in formulas.
   */
  def apply(p: LKProof, formulas: Seq[Formula]): LKProof = withSequentConnector(p, formulas)._1

  /**
   *
   * @param p A proof.
   * @param formulas A list of formulas.
   * @return A new proof whose antecedent contains new occurrences of the formulas in formulas and an SequentConnector.
   */
  def withSequentConnector(p: LKProof, formulas: Seq[Formula]): (LKProof, SequentConnector) = {
    formulas.foldLeft((p, SequentConnector(p.endSequent))) { (acc, f) =>
      val subProof = WeakeningLeftRule(acc._1, f)
      (subProof, subProof.getSequentConnector * acc._2)
    }
  }

  /**
   *
   * @param p An LKProof.
   * @param formula A Formula.
   * @param n A natural number.
   * @return p extended with weakenings such that formula occurs at least n times in the antecedent of the end sequent.
   */
  def apply(p: LKProof, formula: Formula, n: Int): LKProof = withSequentConnector(p, formula, n)._1

  def apply(p: LKProof, formula: Formula): LKProof = apply(p, formula, 1)

  /**
   *
   * @param p An LKProof.
   * @param formula A Formula.
   * @param n A natural number.
   * @return p extended with weakenings such that formula occurs at least n times
   *         in the antecedent of the end sequent and an SequentConnector.
   */
  def withSequentConnector(p: LKProof, formula: Formula, n: Int): (LKProof, SequentConnector) = {
    val nCurrent = p.endSequent.antecedent.count(_ == formula)

    WeakeningLeftMacroRule.withSequentConnector(p, Seq.fill(n - nCurrent)(formula))
  }
}
