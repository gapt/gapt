package at.logic.language.fol;
/*
package at.logic.language.fol.equations

import _root_.at.logic.language.fol._
import _root_.at.logic.language.lambda.types.{->, To, Ti}
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.logicSymbols._


class Equation(function: LambdaExpression, argument: LambdaExpression) extends FOLApp(function, argument) {
  require (function match {
    case App(Var(Equation.equation_symbol, Ti() -> (Ti() -> To()) ), _) =>  true
      case _  => false
    })
}

object Equation {
  val equation_symbol = new ConstantStringSymbol("=")

  def apply(function: LambdaExpression, argument: LambdaExpression) = new Equation(function, argument)

  def apply(term : FOLFormula) = {
    term match {
      case App(function, argument) => new Equation(function, argument)
      case _ => null
    }
  }
}
*/