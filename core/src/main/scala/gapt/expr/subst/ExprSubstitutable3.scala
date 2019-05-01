package gapt.expr.subst

import gapt.expr.ClosedUnderSub
import gapt.expr.Const

trait ExprSubstitutable3 extends ExprSubstitutable2 {
  implicit val ConstClosedUnderSub: ClosedUnderSub[Const] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[Const]
}
