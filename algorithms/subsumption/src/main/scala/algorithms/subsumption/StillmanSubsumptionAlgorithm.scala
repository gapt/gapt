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
import at.logic.language.hol.propositions._

trait StillmanSubsumptionAlgorithm extends SubsumptionAlgorithm {
  val matchAlg: MatchingAlgorithm
  def subsumes(ls1: Tuple2[List[LambdaExpression], List[LambdaExpression]], ls2: Tuple2[List[LambdaExpression], List[LambdaExpression]]): Boolean = 
    ST(ls1._1.map(x => Neg(x.asInstanceOf[Formula])) ++ ls1._2, ls2._1.map(x => Neg(x.asInstanceOf[Formula])) ++ ls2._2, Substitution())

  /* for the case of the second term we replace all variables by constants of the same name), therefore preventing unsound results
   */
  def ST(ls1: List[LambdaExpression], ls2: List[LambdaExpression], sub: LambdaExpression => LambdaExpression): Boolean = ls1 match {
    case Nil => true // first list is exhausted
    case x::ls => val sx = sub(x); ls2.exists(t => matchAlg.matchTerm(sx, ground(t)) match {
      case Some(sub2) => ST(ls, ls2, sub2 compose sub)
      case _ => false
    })
  }

  private def ground(e: LambdaExpression): LambdaExpression = e match {
    case v @ Var(VariableStringSymbol(s),ta) if v.asInstanceOf[Var].isFree => v.factory.createVar(ConstantStringSymbol(s), ta)
    case v: Var => v
    case App(a,b) => App(ground(a), ground(b))
    case abs: Abs => Abs(abs.variable, ground(abs.expressionInScope))
  }
}
