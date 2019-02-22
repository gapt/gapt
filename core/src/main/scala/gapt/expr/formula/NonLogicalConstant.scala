package gapt.expr.formula

import gapt.expr.Const
import gapt.expr.formula.constants.LogicalConstant

object NonLogicalConstant {
  def unapply( c: Const ) = c match {
    case c: LogicalConstant => None
    case Const( n, t, ps )  => Some( ( n, t, ps ) )
  }
}
