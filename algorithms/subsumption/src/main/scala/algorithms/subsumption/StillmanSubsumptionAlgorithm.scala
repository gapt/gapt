/*
 * StillmanSubsumptionAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption

import at.logic.algorithms.matching.MatchingAlgorithm
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.propositions.{Neg => HOLNeg, Formula}
import at.logic.language.fol.{Neg => FOLNeg, FOLFormula}
import at.logic.calculi.lk.base._

trait StillmanSubsumptionAlgorithm extends SubsumptionAlgorithm {
  val matchAlg: MatchingAlgorithm
  def subsumes(s1: Sequent, s2: Sequent): Boolean =
    ST(s1.antecedent.map(x => neg(x)) ++ s1.succedent, s2.antecedent.map(x => neg(x)) ++ s2.succedent, Substitution())

  /* for the case of the second term we replace all variables by constants of the same name), therefore preventing unsound results
   */
  def ST(ls1: List[LambdaExpression], ls2: List[LambdaExpression], sub: LambdaExpression => LambdaExpression): Boolean = ls1 match {
    case Nil => true // first list is exhausted
    case x::ls => val sx = sub(x); ls2.exists(t => matchAlg.matchTerm(sx, t) match {
      case Some(sub2) => ST(ls, ls2, sub2 compose sub)
      case _ => false
    })
  }

  private def neg(f: Formula) = if (f.isInstanceOf[FOLFormula]) FOLNeg(f.asInstanceOf[FOLFormula]) else HOLNeg(f)
}
