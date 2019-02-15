package gapt.expr.formula.hol

import gapt.expr._
import gapt.expr.ty.->:
import gapt.expr.ty.TBase
import gapt.expr.ty.Ty

/**
 * Ordering for HOL Formulas (also for FOL)
 */
object HOLOrdering extends HOLOrdering
class HOLOrdering extends Ordering[Expr] {
  override def compare( x: Expr, y: Expr ): Int = ( x, y ) match {
    case ( x, y ) if x syntaxEquals y => 0
    case ( Var( s1, t1 ), Var( s2, t2 ) ) =>
      s1.toString() compare s2.toString() match {
        case 0 => TAOrdering.compare( t1, t2 )
        case x => x
      }

    case ( Const( s1, t1, _ ), Const( s2, t2, _ ) ) =>
      s1.toString() compare s2.toString() match {
        case 0 => TAOrdering.compare( t1, t2 )
        case x => x
      }

    case ( App( s1, t1 ), App( s2, t2 ) ) =>
      compare( s1, s2 ) match {
        case 0 => compare( t1, t2 )
        case x => x
      }

    case ( Abs( x1, t1 ), Abs( x2, t2 ) ) =>
      compare( x1, x2 ) match {
        case 0 => compare( t1, t2 )
        case x => x
      }

    case ( Var( _, _ ), _ )                => -1

    case ( Const( _, _, _ ), Var( _, _ ) ) => 1
    case ( Const( _, _, _ ), _ )           => -1

    case ( App( _, _ ), Var( _, _ ) )      => 1
    case ( App( _, _ ), Const( _, _, _ ) ) => 1
    case ( App( _, _ ), _ )                => -1

    case ( Abs( _, _ ), Var( _, _ ) )      => 1
    case ( Abs( _, _ ), Const( _, _, _ ) ) => 1
    case ( Abs( _, _ ), App( _, _ ) )      => 1
    case ( Abs( _, _ ), _ )                => -1

    case _                                 => throw new Exception( "Unhandled comparision of hol epxressions: " + x + " ? " + y )
  }
}

/**
 * Ordering on types.
 */
object TAOrdering extends TAOrdering
class TAOrdering extends Ordering[Ty] {
  override def compare( x: Ty, y: Ty ): Int = ( x, y ) match {
    case ( x, y ) if x == y => 0
    case ( t1 ->: t2, t3 ->: t4 ) =>
      val r = compare( t1, t3 )
      if ( r == 0 ) compare( t2, t4 ) else r
    case ( _, _ ->: _ )                     => -1
    case ( _ ->: _, _ )                     => 1

    case ( TBase( x_, _ ), TBase( y_, _ ) ) => x_ compare y_
  }
}
