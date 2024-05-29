package gapt.expr.formula

import gapt.expr.App
import gapt.expr.Apps
import gapt.expr.Expr
import gapt.expr.formula.constants.MonomorphicLogicalC
import gapt.expr.formula.fol.FOLExpression
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.prop.PropFormula

class UnaryPropConnectiveHelper(val c: MonomorphicLogicalC) {
  def apply(a: Expr): Formula = Apps(c(), a).asInstanceOf[Formula]
  def apply(a: FOLFormula): FOLFormula = apply(a.asInstanceOf[Expr]).asInstanceOf[FOLFormula]
  def apply(a: PropFormula): PropFormula = apply(a.asInstanceOf[Expr]).asInstanceOf[PropFormula]

  def unapply(formula: Expr): Option[Formula] = formula match {
    case App(c(), a: Formula) => Some(a)
    case _                    => None
  }
  def unapply(formula: FOLFormula): Option[FOLFormula] =
    unapply(formula.asInstanceOf[FOLExpression])
  def unapply(formula: FOLExpression): Option[FOLFormula] =
    unapply(formula.asInstanceOf[Expr]) match {
      case Some(a: FOLFormula) => Some(a)
      case _                   => None
    }
  def unapply(formula: PropFormula): Option[PropFormula] =
    unapply(formula.asInstanceOf[Expr]) match {
      case Some(a: PropFormula) => Some(a)
      case _                    => None
    }
}
