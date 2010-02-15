/*
 * MatchingAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.matching

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._

trait MatchingAlgorithm {
  def matchTerm(term: LambdaExpression, posInstance: LambdaExpression): Option[Substitution]
  // in all instances of the algorithm we ground the second term by replacing all free variables by constants
  protected def ground(e: LambdaExpression): LambdaExpression = e match {
    case v @ Var(VariableStringSymbol(s),ta) if v.asInstanceOf[Var].isFree => v.factory.createVar(ConstantStringSymbol(s), ta)
    case v: Var => v
    case App(a,b) => App(ground(a), ground(b))
    case abs: Abs => Abs(abs.variable, ground(abs.expressionInScope))
  }
}