package at.logic.gapt.language.hol.algorithms.simplify

import at.logic.gapt.language.hol._

object simplify {
  def apply( f: HOLFormula ): HOLFormula = f match {
    case HOLAnd( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( HOLTopC, r )     => r
      case ( r, HOLTopC )     => r
      case ( HOLBottomC, _ )  => HOLBottomC
      case ( _, HOLBottomC )  => HOLBottomC
      case ( l, r ) if l == r => l
      case ( l, r )           => HOLAnd( l, r )
    }
    case HOLOr( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( HOLTopC, _ )     => HOLTopC
      case ( _, HOLTopC )     => HOLTopC
      case ( HOLBottomC, r )  => r
      case ( r, HOLBottomC )  => r
      case ( l, r ) if l == r => l
      case ( l, r )           => HOLOr( l, r )
    }
    case HOLImp( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( HOLTopC, r )     => r
      case ( _, HOLTopC )     => HOLTopC
      case ( HOLBottomC, _ )  => HOLTopC
      case ( r, HOLBottomC )  => simplify( HOLNeg( r ) )
      case ( l, r ) if l == r => HOLTopC
      case ( l, r )           => HOLImp( l, r )
    }
    case HOLNeg( s ) => simplify( s ) match {
      case HOLTopC    => HOLBottomC
      case HOLBottomC => HOLTopC
      case s          => HOLNeg( s )
    }
    case _ => f
  }
}
