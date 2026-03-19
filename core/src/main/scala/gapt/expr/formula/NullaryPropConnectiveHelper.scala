package gapt.expr.formula

import gapt.expr.Const
import gapt.expr.formula.constants.MonomorphicLogicalC
import gapt.expr.formula.prop.PropFormula

class NullaryPropConnectiveHelper(val c: MonomorphicLogicalC) {
  def apply(): PropFormula & Const = c().asInstanceOf[PropFormula & Const]
  def unapply(formula: PropFormula): Boolean = c() == formula
}
