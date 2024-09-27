package gapt.proofs.lk.rules.macros

import gapt.expr.formula.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ConvenienceConstructor

/**
 * This macro rule simulates multiple weakenings and contractions in both cedents.
 *
 */
object WeakeningContractionMacroRule extends ConvenienceConstructor("WeakeningContractionMacroRule") {

  /**
   *
   * @param p An LKProof.
   * @param antMap Map of type Formula => Int that expresses “f should occur n times in the antecedent”.
   * @param sucMap Map of type Formula => Int that expresses “f should occur n times in the succedent”.
   * @param strict If true: requires that for f -> n in antMap or sucMap, if f occurs in the root of s1, then n > 0.
   * @return
   */
  def apply(p: LKProof, antMap: Map[Formula, Int], sucMap: Map[Formula, Int], strict: Boolean): LKProof = {
    val currentAnt = p.endSequent.antecedent
    val currentSuc = p.endSequent.succedent

    val subProof = antMap.foldLeft(p)((acc, p) => {
      val (f, n) = p
      val nCurrent = currentAnt.count(_ == f)
      if (n == 0 && nCurrent != 0 && strict)
        throw LKRuleCreationException("Cannot erase formula occurrences.")

      if (n > nCurrent)
        WeakeningLeftMacroRule(acc, f, n - nCurrent)
      else if (n == nCurrent)
        acc
      else // n < nCurrent
        ContractionLeftMacroRule(acc, f, n)
    })

    sucMap.foldLeft(subProof)((acc, p) => {
      val (f, n) = p
      val nCurrent = currentSuc.count(_ == f)
      if (n == 0 && nCurrent != 0 && strict)
        throw LKRuleCreationException("Cannot erase formula occurrences.")

      if (n > nCurrent)
        WeakeningRightMacroRule(acc, f, n - nCurrent)
      else if (n == nCurrent)
        acc
      else // n < nCurrent
        ContractionRightMacroRule(acc, f, n)
    })
  }

  /**
   *
   * @param p An LKProof.
   * @param antMap Map of type Formula => Int that expresses “f should occur n times in the antecedent”.
   * @param sucMap Map of type Formula => Int that expresses “f should occur n times in the succedent”.
   * @param strict If true: requires that for f -> n in antMap or sucMap, if f occurs in the root of s1, then n > 0.
   * @return A proof and an SequentConnector connecting its end sequent to the end sequent of p.
   */
  def withSequentConnector(
      p: LKProof,
      antMap: Map[Formula, Int],
      sucMap: Map[Formula, Int],
      strict: Boolean
  ): (LKProof, SequentConnector) = {
    val currentAnt = p.endSequent.antecedent
    val currentSuc = p.endSequent.succedent

    val (subProof, subConnector) = antMap.foldLeft((p, SequentConnector(p.endSequent))) { (acc, x) =>
      val (f, n) = x
      val nCurrent = currentAnt.count(_ == f)
      if (n == 0 && nCurrent != 0 && strict)
        throw LKRuleCreationException("Cannot erase formula occurrences.")

      if (n > nCurrent) {
        val (subProof_, subConnector_) = WeakeningLeftMacroRule.withSequentConnector(acc._1, f, n)
        (subProof_, subConnector_ * acc._2)
      } else if (n == nCurrent)
        acc
      else { // n < nCurrent
        val (subProof_, subConnector_) = ContractionLeftMacroRule.withSequentConnector(acc._1, f, n)
        (subProof_, subConnector_ * acc._2)
      }
    }

    sucMap.foldLeft((subProof, subConnector)) { (acc, x) =>
      val (f, n) = x
      val nCurrent = currentSuc.count(_ == f)
      if (n == 0 && nCurrent != 0 && strict)
        throw LKRuleCreationException("Cannot erase formula occurrences.")

      if (n > nCurrent) {
        val (subProof_, subConnector_) = WeakeningRightMacroRule.withSequentConnector(acc._1, f, n)
        (subProof_, subConnector_ * acc._2)
      } else if (n == nCurrent)
        acc
      else { // n < nCurrent
        val (subProof_, subConnector_) = ContractionRightMacroRule.withSequentConnector(acc._1, f, n)
        (subProof_, subConnector_ * acc._2)
      }
    }
  }

  /**
   *
   * @param p An LKProof.
   * @param targetSequent The proposed end sequent.
   * @param strict If true, will require that the end sequent of p contains no formula
   *               that doesn't appear at least once in targetSequent.
   * @return p with its end sequent modified to targetSequent by means of weakening and contraction.
   */
  def apply(p: LKProof, targetSequent: HOLSequent, strict: Boolean = true): LKProof =
    withSequentConnector(p, targetSequent, strict)._1

  /**
   *
   * @param p An LKProof.
   * @param targetSequent The proposed end sequent.
   * @param strict If true, will require that the end sequent of p contains no formula that
   *               doesn't appear at least once in targetSequent.
   * @return p with its end sequent modified to targetSequent by means of
   *         weakening and contraction and an SequentConnector.
   */
  def withSequentConnector(p: LKProof, targetSequent: HOLSequent, strict: Boolean = true): (LKProof, SequentConnector) = {
    val currentSequent = p.endSequent
    val targetAnt = targetSequent.antecedent
    val targetSuc = targetSequent.succedent

    if (strict && !(currentSequent isSubsetOf targetSequent))
      throw LKRuleCreationException(
        s"""Sequent $targetSequent cannot be reached from $currentSequent by weakenings and contractions:
           |It is missing the following formulas:
           |${currentSequent.distinct diff targetSequent.distinct}
         """.stripMargin
      )

    val antList = targetAnt.distinct map (f => (f, targetAnt.count(_ == f)))
    val sucList = targetSuc.distinct map (f => (f, targetSuc.count(_ == f)))

    withSequentConnector(p, Map(antList: _*), Map(sucList: _*), strict)
  }
}
