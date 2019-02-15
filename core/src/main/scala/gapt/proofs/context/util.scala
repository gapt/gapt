package gapt.proofs.context

import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.formula.Eq
import gapt.expr.preExpr
import gapt.expr.util.syntacticMatching
import gapt.formats.babel.BabelParser

private[context] object parseDefinitionalEquation {

  def apply(
    c: Const, equation: String )( implicit ctx: Context ): ( Expr, Expr ) = {
    BabelParser.tryParse(
      equation,
      p => preExpr.TypeAnnotation( p, preExpr.Bool ) )
      .fold( throw _, identity ) match {
        case Eq( lhs @ Apps( c_, _ ), rhs ) =>
          syntacticMatching( c_, c ).get( lhs -> rhs )
      }
  }

}
