package gapt.provers.viper

import gapt.expr.{ Apps, Const, Expr }
import gapt.expr.formula.{ Formula, Neg }
import gapt.expr.ty.{ TArr, Ty }
import gapt.proofs.context.Context

package object spin {

  // Replaces x with e in f.
  def replaceExpr( f: Expr, x: Expr, e: Expr ): Expr =
    f.find( x ).foldLeft( f )( ( f, pos ) => f.replace( pos, e ) )

  def negate( f: Formula ): Formula = f match {
    case Neg( g ) => g
    case _        => Neg( f )
  }

  def resType( ty: Ty ): Ty =
    ty match {
      case TArr( _, t ) => resType( t )
      case _            => ty
    }

  // Is c a constructor
  def isConstructor( c: Const )( implicit ctx: Context ): Boolean =
    ctx.getConstructors( resType( c.ty ) ) match {
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

  def lambdaType( t: String ): Boolean = t.matches( "fun[0-9]+" )

  def funHeaded( e: Expr )( implicit ctx: Context ): Boolean =
    e match {
      case Apps( c @ Const( _, _, _ ), _ ) =>
        ctx.conditionalNormalizer.rewriteRules.exists( _.lhsHead == c ) && !lambdaType( c.ty.toString )
      case _ => false
    }

}
