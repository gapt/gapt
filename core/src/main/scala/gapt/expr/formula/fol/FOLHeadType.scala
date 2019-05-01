package gapt.expr.formula.fol

import gapt.expr.ty.->:
import gapt.expr.ty.Ti
import gapt.expr.ty.Ty

object FOLHeadType {
  def apply( ret: Ty, arity: Int ): Ty = arity match {
    case 0 => ret
    case n => Ti ->: FOLHeadType( ret, n - 1 )
  }
  def unapply( t: Ty ): Option[( Ty, Int )] = t match {
    case Ti ->: FOLHeadType( t, n ) => Some( ( t, n + 1 ) )
    case _                          => Some( ( t, 0 ) )
  }
}
