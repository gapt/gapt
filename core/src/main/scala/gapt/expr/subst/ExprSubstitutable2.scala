package gapt.expr.subst

import gapt.expr.ClosedUnderSub
import gapt.expr.Formula

trait ExprSubstitutable2 extends ExprSubstitutable1 {
  implicit val FormulaClosedUnderSub: ClosedUnderSub[Formula] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[Formula]
}
