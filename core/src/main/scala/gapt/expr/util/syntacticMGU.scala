package gapt.expr.util

import gapt.expr.->:
import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.FOLExpression
import gapt.expr.FOLSubstitution
import gapt.expr.PreSubstitution
import gapt.expr.Substitution
import gapt.expr.TBase
import gapt.expr.TVar
import gapt.expr.TermReplacement
import gapt.expr.Ty
import gapt.expr.Var
import gapt.utils.UNone
import gapt.utils.UOption
import gapt.utils.USome

object syntacticMGU {

  private def go( a: Ty, b: Ty, subst: PreSubstitution, bound: Set[Var] ): UOption[PreSubstitution] =
    ( a, b ) match {
      case _ if a eq b => USome( subst )

      case ( a1 ->: a2, b1 ->: b2 ) =>
        go( a1, b1, subst, bound ) match {
          case USome( subst1 ) => go( a2, b2, subst1, bound )
          case _               => UNone()
        }

      case ( TBase( n1, ts1 ), TBase( n2, ts2 ) ) =>
        if ( n1 != n2 ) UNone() else go( ts1, ts2, subst, bound )

      case ( x: TVar, t ) =>
        subst.typeMap.get( x ) match {
          case Some( x_ ) => go( x_, t, subst, bound )
          case None =>
            val t_ = subst.toSubstitution( t )
            if ( x == t_ ) {
              USome( subst )
            } else if ( typeVariables( t_ ).contains( x ) ) {
              UNone()
            } else {
              val subst1 = Substitution( Map(), Map( x -> t_ ) )
              USome( new PreSubstitution(
                Map() ++ subst.map.mapValues( subst1( _ ) ),
                Map() ++ subst.typeMap.mapValues( subst1( _ ) ) + ( x -> t_ ) ) )
            }
        }

      case ( y, x: TVar ) => go( x, y, subst, bound )

      case _              => UNone()
    }

  private def go( as: List[Ty], bs: List[Ty], subst: PreSubstitution, bound: Set[Var] ): UOption[PreSubstitution] =
    ( as, bs ) match {
      case ( Nil, Nil ) => USome( subst )
      case ( a :: ass, b :: bss ) =>
        go( a, b, subst, bound ) match {
          case USome( subst1 ) => go( ass, bss, subst1, bound )
          case _               => UNone()
        }
      case _ => UNone()
    }

  private def go( a: Expr, b: Expr, subst: PreSubstitution, bound: Set[Var] ): UOption[PreSubstitution] =
    ( a, b ) match {
      case _ if a eq b => USome( subst )

      case ( App( a1, a2 ), App( b1, b2 ) ) =>
        go( a1, b1, subst, bound ) match {
          case USome( subst1 ) =>
            go( a2, b2, subst1, bound )
          case _ => UNone()
        }

      case ( Const( n1, t1, ps1 ), Const( n2, t2, ps2 ) ) =>
        if ( n1 != n2 ) UNone() else
          go( t1, t2, subst, bound ) match {
            case USome( subst1 ) =>
              go( ps1, ps2, subst1, bound )
            case _ => UNone()
          }

      case ( Abs( v1, e1 ), Abs( v2, e2 ) ) =>
        if ( v1.ty == v2.ty ) {
          val v1_ = rename( v1, subst.domain ++ subst.range ++ freeVariables( List( a, b ) ) )
          val v2_ = v1_
          go( Substitution( v1 -> v1_ )( e1 ), Substitution( v2 -> v2_ )( e2 ), subst, bound + v1_ ).
            map( subst2 => new PreSubstitution( subst2.map - v1_, subst2.typeMap ) )
        } else go( v1.ty, v2.ty, subst, bound ) match {
          case USome( subst1 ) =>
            val subst1_ = subst1.toSubstitution
            go( subst1_( a ), subst1_( b ), subst1, bound )
          case _ => UNone()
        }

      case ( x: Var, y ) if bound.contains( x ) =>
        if ( x == y ) USome( subst ) else UNone()

      case ( x: Var, t ) =>
        subst.map.get( x ) match {
          case Some( x_ ) => go( x_, t, subst, bound )
          case None =>
            val t_ = subst.toSubstitution( t )
            if ( x == t_ ) {
              USome( subst )
            } else if ( freeVariables( t_ ) intersect ( bound + x ) nonEmpty ) {
              UNone()
            } else if ( x.ty == t_.ty ) {
              val subst1 = Substitution( x -> t_ )
              USome( new PreSubstitution( Map() ++ subst.map.mapValues( subst1( _ ) ) + ( x -> t_ ), subst.typeMap ) )
            } else {
              go( x.ty, t_.ty, subst, bound ) match {
                case USome( subst1 ) =>
                  val subst1_ = subst1.toSubstitution
                  go( subst1_( x ), subst1_( t_ ), subst, bound )
                case _ => UNone()
              }
            }
        }

      case ( y, x: Var ) => go( x, y, subst, bound )

      case _             => UNone()
    }

  def apply( exprs: Iterable[Expr] )( implicit dummyImplicit: DummyImplicit ): Option[Substitution] = {
    val exprs_ = exprs.toSeq
    apply( exprs_ zip exprs_.tail )
  }
  def apply( eqs: Iterable[( Expr, Expr )] ): Option[Substitution] = {
    var subst: UOption[PreSubstitution] = USome( PreSubstitution() )
    eqs.foreach { case ( l, r ) => subst = subst.flatMap( go( l, r, _, Set.empty[Var] ) ) }
    subst.map( _.toSubstitution ).toOption
  }
  def apply( a: Expr, b: Expr ): Option[Substitution] =
    go( a, b, PreSubstitution(), Set.empty[Var] ).
      map( _.toSubstitution ).toOption

  def apply( eqs: Iterable[( FOLExpression, FOLExpression )] )( implicit dummyImplicit: DummyImplicit, dummyImplicit2: DummyImplicit ): Option[FOLSubstitution] =
    apply( eqs: Iterable[( Expr, Expr )] ).map( _.asFOLSubstitution )
  def apply( a: FOLExpression, b: FOLExpression ): Option[FOLSubstitution] =
    apply( a: Expr, b ).map( _.asFOLSubstitution )

  def apply( a: Expr, b: Expr, treatAsConstant: Set[Var] ): Option[Substitution] = {
    val nameGen = rename.awayFrom( constants( a ) ++ constants( b ) )
    val grounding = treatAsConstant.map( v => v -> nameGen.fresh( Const( v.name, v.ty ) ) )
    apply( Substitution( grounding )( a ), Substitution( grounding )( b ) ).map( mgu =>
      TermReplacement( mgu, grounding.map( _.swap ).toMap ) )
  }

}
