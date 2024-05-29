package gapt.proofs.lk.rules.macros

import gapt.expr.formula.Formula
import gapt.proofs.SequentConnector
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ContractionLeftRule

/**
 * This macro rule simulates a series of contractions in the antecedent.
 *
 */
object ContractionLeftMacroRule {

  /**
   *
   * @param p A proof.
   * @param occs A list of occurrences of a Formula in the antecedent of s1.
   * @return A proof ending with as many contraction rules as necessary to contract occs into a single occurrence.
   */
  def apply(p: LKProof, occs: Seq[SequentIndex]): LKProof = withSequentConnector(p, occs)._1

  /**
   *
   * @param p A proof.
   * @param occs A list of occurrences of a Formula in the antecedent of s1.
   * @return A proof ending with as many contraction rules as necessary to contract occs into a
   *         single occurrence and an SequentConnector.
   */
  def withSequentConnector(p: LKProof, occs: Seq[SequentIndex]): (LKProof, SequentConnector) =
    occs.sorted.reverse match {
      case Seq() | _ +: Seq() => (p, SequentConnector(p.endSequent))
      case occ1 +: rest =>
        val occ2 = rest.head
        val (subProof, subConnector) = withSequentConnector(p, rest)
        val proof = ContractionLeftRule(subProof, subConnector.child(occ1), subConnector.child(occ2))
        (proof, proof.getSequentConnector * subConnector)
    }

  /**
   * Contracts one formula in the antecedent down to n occurrences. Use with care!
   *
   * @param p A proof.
   * @param form A formula.
   * @param n Maximum number of occurrences of form in the antecedent of the end sequent.
   *          Defaults to 1, i.e. all occurrences are contracted.
   * @return
   */
  def apply(p: LKProof, form: Formula, n: Int = 1): LKProof =
    withSequentConnector(p, form, n)._1

  /**
   * Contracts one formula in the antecedent down to n occurrences. Use with care!
   *
   * @param p A proof.
   * @param form A formula.
   * @param n Maximum number of occurrences of form in the antecedent of the end sequent.
   *          Defaults to 1, i.e. all occurrences are contracted.
   * @return A proof and an SequentConnector connecting its end sequent with the end sequent of p.
   */
  def withSequentConnector(p: LKProof, form: Formula, n: Int = 1): (LKProof, SequentConnector) = {
    if (n < 1) throw new IllegalArgumentException("n must be >= 1.")
    val list = p.endSequent.indicesWhere(_ == form).filter(_.isAnt).drop(n - 1)

    withSequentConnector(p, list)
  }
}
