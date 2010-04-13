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
import at.logic.language.hol._
import at.logic.language.fol.{Neg => FOLNeg, FOLFormula}
import at.logic.calculi.lk.base._

trait StillmanSubsumptionAlgorithm[T <: LambdaExpression] extends SubsumptionAlgorithm {
  val matchAlg: MatchingAlgorithm[T]
  def subsumes(s1: Sequent, s2: Sequent): Boolean =
    ST(s1.antecedent.map(x => neg(x)) ++ s1.succedent, s2.antecedent.map(x => neg(x)) ++ s2.succedent, Substitution(), (s2.antecedent.flatMap(x => x.getFreeAndBoundVariables._1) ++ s2.succedent.flatMap(x => x.getFreeAndBoundVariables._1)).toList)

  def ST(ls1: List[LambdaExpression], ls2: List[LambdaExpression], sub: T => T, restrictedDomain: List[Var]): Boolean = ls1 match {
    case Nil => true // first list is exhausted
    case x::ls => val sx = sub(x.asInstanceOf[T]); ls2.exists(t => matchAlg.matchTerm(sx.asInstanceOf[T], sub(t.asInstanceOf[T]), restrictedDomain) match {
      case Some(sub2) => ST(ls, ls2, sub2 compose sub, restrictedDomain)
      case _ => false
    })
  }

  // should be generic but right now supports only hol and fol
  private def neg(f: Formula) = if (f.isInstanceOf[FOLFormula]) FOLNeg(f.asInstanceOf[FOLFormula]) else Neg(f.asInstanceOf[HOLFormula])
}
