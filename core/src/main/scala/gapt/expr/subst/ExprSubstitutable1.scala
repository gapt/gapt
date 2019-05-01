package gapt.expr.subst

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.ClosedUnderSub
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.ty.->:
import gapt.expr.ty.TBase
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty
import gapt.expr.util.freeVariables
import gapt.expr.util.rename

trait ExprSubstitutable1 {
  implicit object SubstitutableTy extends ClosedUnderSub[Ty] {
    override def applySubstitution( sub: Substitution, ty: Ty ): Ty =
      applySubstitution( sub: PreSubstitution, ty )
    def applySubstitution( sub: PreSubstitution, ty: Ty ): Ty = ty match {
      case _ if sub.typeMap.isEmpty => ty
      case ty @ TBase( _, Nil )     => ty
      case TBase( n, ps )           => TBase( n, ps.map( applySubstitution( sub, _ ) ) )
      case in ->: out               => applySubstitution( sub, in ) ->: applySubstitution( sub, out )
      case v @ TVar( _ )            => sub.typeMap.getOrElse( v, v )
    }
  }

  /**
   * The general method for applying substitutions to lambda expressions.
   *
   * @param sub A substitution.
   * @param t A lambda expression.
   * @return The substituted lambda expression.
   */
  protected def applySub( sub: Substitution, t: Expr ): Expr =
    if ( sub.isIdentity ) t else {
      val sub1 = if ( sub.typeMap.isEmpty ) sub else {
        Substitution(
          freeVariables( t ).map( v => v -> sub.applyToTypeOnly( v ) ).toMap ++ sub.map,
          sub.typeMap )
      }
      go( sub1, t )
    }

  // if sub.typeMap.nonEmpty, then every free variable must in the domain of sub
  private def go( sub: Substitution, t: Expr ): Expr = t match {
    case _ if sub.isEmpty => t
    case v: Var           => sub( v )
    case c @ Const( x, ty, ps ) =>
      if ( sub.typeMap.isEmpty ) c else
        Const( x, SubstitutableTy.applySubstitution( sub, ty ),
          ps.map( SubstitutableTy.applySubstitution( sub, _ ) ) )
    case App( a, b ) => App( go( sub, a ), go( sub, b ) )
    case Abs( v, _ ) if sub.domain contains v =>
      go( Substitution( sub.map - v, sub.typeMap ), t )
    case Abs( v, s ) if sub.range contains sub.applyToTypeOnly( v ) =>
      // It is safe to rename the bound variable to any variable that is not in freeVariables(s).
      val newV = rename( v, freeVariables( s ) union sub.range )
      applySub( sub, Abs( newV, applySub( Substitution( v -> newV ), s ) ) )
    case Abs( v, s ) =>
      val newV = sub.applyToTypeOnly( v )
      Abs( newV, go( Substitution( sub.map + ( v -> newV ), sub.typeMap ), s ) )
  }

  implicit val ExprClosedUnderSub: ClosedUnderSub[Expr] =
    ( sub, t ) => applySub( sub, t )
}
