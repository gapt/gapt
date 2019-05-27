package gapt.provers.viper

import gapt.expr.{ Const, Expr }
import gapt.expr.formula.{ Formula, Neg }
import gapt.expr.ty.Ty
import gapt.proofs.context.Context

package object spin {

  // Replaces x with e in f.
  def replaceExpr( f: Expr, x: Expr, e: Expr ): Expr =
    f.find( x ).foldLeft( f )( ( f, pos ) => f.replace( pos, e ) )

  def negate( f: Formula ): Formula = f match {
    case Neg( g ) => g
    case _        => Neg( f )
  }

  // Is c a constructor
  def isConstructor( t: Ty, c: Const )( implicit ctx: Context ): Boolean =
    ctx.getConstructors( t ) match {
      case None            => false
      case Some( constrs ) => constrs.contains( c )
    }

  // Is c an inductive skolem constant, i.e. not a constructor
  def isInductive( c: Const )( implicit ctx: Context ): Boolean =
    ctx.getConstructors( c.ty ) match {
      case None => false
      case Some( constrs ) =>
        !constrs.contains( c ) && !ctx.conditionalNormalizer.rewriteRules.exists( rule => rule.lhsHead == c )
    }

  def asInductiveConst( e: Expr )( implicit ctx: Context ): Option[Const] =
    e match {
      case c @ Const( _, _, _ ) if isInductive( c ) => Some( c )
      case _                                        => None
    }

}
