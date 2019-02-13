package gapt.expr.subst

import gapt.expr.Abs
import gapt.expr.ClosedUnderSub
import gapt.expr.Expr
import gapt.expr.Formula

trait ExprSubstWithβ1 extends ExprSubstWithβ0 {
  implicit val formulaSubstWithβ: ClosedUnderSub[Formula] =
    ( sub, formula ) => sub( formula: Expr ).asInstanceOf[Formula]
  implicit val absSubstWithβ: ClosedUnderSub[Abs] =
    ( sub, abs ) => sub( abs: Expr ).asInstanceOf[Abs]
}
