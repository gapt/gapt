package gapt.proofs.lk.rules.macros

import gapt.expr.formula.All
import gapt.expr.formula.Ex
import gapt.expr.formula.hol.isPrenex
import gapt.proofs.expansion.ETWeakQuantifier
import gapt.proofs.expansion.ExpansionSequent
import gapt.proofs.expansion.ExpansionTree
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ForallLeftRule

/**
 * Computes a proof of F from a proof of some instances of F
 *
 */
object proofFromInstances {

  /**
   *
   * @param s1 An LKProof containing the instances in es in its end sequent.
   * @param es An ExpansionSequent in which all shallow formulas are prenex
   *           and which contains no strong or Skolem quantifiers.
   * @return A proof starting with s1 and ending with the deep sequent of es.
   */
  def apply(s1: LKProof, es: ExpansionSequent): LKProof =
    (es.antecedent ++ es.succedent).foldLeft(s1)(apply)

  /**
   *
   * @param s1 An LKProof containing the instances in et in its end sequent
   * @param et A ExpansionTree whose shallow formula is prenex and which contains no strong or Skolem quantifiers.
   * @return A proof starting with s1 and ending with the deep formula of met.
   */
  def apply(s1: LKProof, et: ExpansionTree): LKProof = {
    require(isPrenex(et.shallow), "Shallow formula of " + et + " is not prenex")

    et match {
      case ETWeakQuantifier(f @ All(_, _), instances) =>
        val tmp = instances.foldLeft(s1) {
          (acc, i) => ForallLeftRule(apply(acc, i._2), f, i._1)
        }

        ContractionLeftMacroRule(tmp, f)

      case ETWeakQuantifier(f @ Ex(_, _), instances) =>
        val tmp = instances.foldLeft(s1) {
          (acc, i) => ExistsRightRule(apply(acc, i._2), f, i._1)
        }

        ContractionRightMacroRule(tmp, f)

      case _ => s1
    }
  }
}
