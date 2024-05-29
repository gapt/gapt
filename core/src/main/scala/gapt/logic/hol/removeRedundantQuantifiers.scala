package gapt.logic.hol

import gapt.expr.{Abs, App, Expr}
import gapt.expr.formula.Quant

object removeRedundantQuantifiers {

  /**
   * Removes ∀ and ∃ quantifiers which bind a variable that does not occur in the inner formula.
   *
   * @param expression expression of which to remove redundant quantifiers
   * @tparam T type of the expression
   * @return equivalent expression that does not contain redundant quantifiers
   */
  def apply[T <: Expr](expression: T): T = (expression match {
    case Quant(variable, innerFormula, _) if !innerFormula.contains(variable) =>
      removeRedundantQuantifiers(innerFormula)
    case App(function, argument) =>
      App(removeRedundantQuantifiers(function), removeRedundantQuantifiers(argument))
    case Abs(variable, innerExpression) =>
      Abs(variable, removeRedundantQuantifiers(innerExpression))
    case _ => expression
  }).asInstanceOf[T]
}
