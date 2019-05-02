package gapt.expr.formula

import gapt.expr.Const
import gapt.expr.formula.constants.LogicalConstant
import gapt.expr.ty.Ty

object NonLogicalConstant {
  def unapply( c: Const ): Option[( String, Ty, List[Ty] )] = c match {
    case c: LogicalConstant => None
    case Const( n, t, ps )  => Some( ( n, t, ps ) )
  }
}
