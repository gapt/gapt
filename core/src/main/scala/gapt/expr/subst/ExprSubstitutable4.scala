package gapt.expr.subst

import gapt.expr.ClosedUnderFOLSub
import gapt.expr.FOLExpression

trait ExprSubstitutable4 extends ExprSubstitutable3 {
  implicit val FOLExpressionClosedUnderFOLSub: ClosedUnderFOLSub[FOLExpression] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[FOLExpression]
}
