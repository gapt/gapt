package gapt.expr.formula

import gapt.expr.Expr
import gapt.expr.formula.hol.HOLPosition

trait Formula extends Expr {
  override def replace( pos: HOLPosition, exp: Expr ) = HOLPosition.replace( this, pos, exp )
}
