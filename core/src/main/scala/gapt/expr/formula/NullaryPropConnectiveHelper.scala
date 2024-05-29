package gapt.expr.formula

import gapt.expr.Const
import gapt.expr.formula.constants.MonomorphicLogicalC
import gapt.expr.formula.prop.PropFormula

class NullaryPropConnectiveHelper(val c: MonomorphicLogicalC) {
  def apply(): PropFormula with Const = c().asInstanceOf[PropFormula with Const]
  def unapply(formula: PropFormula): Boolean = c() == formula
}
