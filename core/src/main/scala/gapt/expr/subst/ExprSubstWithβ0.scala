package gapt.expr.subst

import gapt.expr.Abs
import gapt.expr.BetaReduction
import gapt.expr.ClosedUnderSub
import gapt.expr.Expr

trait ExprSubstWithβ0 {
  implicit val exprSubstWithβ: ClosedUnderSub[Expr] = ( sub, expr ) => {
    val substituted = sub( expr )( Substitutable.ExprClosedUnderSub )
    val needβ = sub.map.values.exists( _.isInstanceOf[Abs] )
    if ( needβ ) BetaReduction.betaNormalize( substituted ) else substituted
  }
}
