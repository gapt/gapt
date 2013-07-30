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
import at.logic.calculi.lk.base.types._

trait StillmanSubsumptionAlgorithm[T <: LambdaExpression] extends SubsumptionAlgorithm {
  val matchAlg: MatchingAlgorithm[T]
  def subsumes(s1: FSequent, s2: FSequent): Boolean =
    ST(s1._1.map(x => neg(x)) ++ s1._2.map(x => x),
      s2._1.map(x => neg(x)) ++ s2._2.map(x => x), 
      Substitution(), 
      (s2._1.flatMap(x => x.freeVariables) ++ s2._2.flatMap(x => x.freeVariables)).toList)

  def ST(ls1: Seq[LambdaExpression], ls2: Seq[LambdaExpression], sub: T => T, restrictedDomain: List[Var]): Boolean = ls1 match {
    case Nil => true // first list is exhausted
    case x::ls => val sx = sub(x.asInstanceOf[T]); ls2.exists(t => matchAlg.matchTerm(sx.asInstanceOf[T], sub(t.asInstanceOf[T]), restrictedDomain) match {
      case Some(sub2) => ST(ls, ls2, sub2 compose sub, restrictedDomain)
      case _ => false
    })
  }

  // should be generic but right now supports only hol and fol
  private def neg(f: Formula) = if (f.isInstanceOf[FOLFormula]) FOLNeg(f.asInstanceOf[FOLFormula]) else Neg(f.asInstanceOf[HOLFormula])
}
