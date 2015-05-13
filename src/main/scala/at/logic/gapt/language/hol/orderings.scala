package at.logic.gapt.language.hol

import at.logic.gapt.expr._
import at.logic.gapt.expr._

/**
 * Ordering for HOL Formulas (also for FOL)
 */
object HOLOrdering extends HOLOrdering
class HOLOrdering extends Ordering[LambdaExpression] {
  override def compare( x: LambdaExpression, y: LambdaExpression ): Int = ( x, y ) match {
    case ( x, y ) if x syntaxEquals y => 0
    case ( Var( s1, t1 ), Var( s2, t2 ) ) =>
      s1.toString() compare s2.toString() match {
        case 0 => TAOrdering.compare( t1, t2 )
        case x => x
      }

    case ( Const( s1, t1 ), Const( s2, t2 ) ) =>
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

    case ( Var( _, _ ), _ )             => -1

    case ( Const( _, _ ), Var( _, _ ) ) => 1
    case ( Const( _, _ ), _ )           => -1

    case ( App( _, _ ), Var( _, _ ) )   => 1
    case ( App( _, _ ), Const( _, _ ) ) => 1
    case ( App( _, _ ), _ )             => -1

    case ( Abs( _, _ ), Var( _, _ ) )   => 1
    case ( Abs( _, _ ), Const( _, _ ) ) => 1
    case ( Abs( _, _ ), App( _, _ ) )   => 1
    case ( Abs( _, _ ), _ )             => -1

    case _                              => throw new Exception( "Unhandled comparision of hol epxressions: " + x + " ? " + y )
  }
}

/**
 * Ordering on types.
 */
object TAOrdering extends TAOrdering
class TAOrdering extends Ordering[TA] {
  override def compare( x: TA, y: TA ): Int = ( x, y ) match {
    case ( x, y ) if x == y => 0
    case ( t1 -> t2, t3 -> t4 ) =>
      val r = compare( t1, t3 )
      if ( r == 0 ) compare( t2, t4 ) else r
    case ( _, _ -> _ )  => -1
    case ( _ -> _, _ )  => 1

    //o < i < index
    case ( To, Ti )     => -1
    case ( To, Tindex ) => -1

    case ( Ti, To )     => 1
    case ( Ti, Tindex ) => -1

    case ( Tindex, Ti ) => 1
    case ( Tindex, To ) => 1
    case _              => throw new Exception( "Unhandled case in type comparison: " + x + " ? " + y )
  }
}
