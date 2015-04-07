package at.logic.gapt.language.fol.algorithms.simplify

import at.logic.gapt.language.fol._

// TODO: this is copy'n'paste from HOL; done since the 
// logical constants in HOL/FOL are different. Reimplement
// this on top of the HOL algorithm once the superflous
// copies of the logical constants have been deleted by
// refactoring.
object simplify {
  def apply( f: FOLFormula ): FOLFormula = f match {
    case FOLAnd( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( FOLTopC, r )        => r
      case ( r, FOLTopC )        => r
      case ( FOLBottomC, _ )     => FOLBottomC
      case ( _, FOLBottomC )     => FOLBottomC
      case ( l, r ) if l == r => l
      case ( l, r )           => FOLAnd( l, r )
    }
    case FOLOr( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( FOLTopC, _ )        => FOLTopC
      case ( _, FOLTopC )        => FOLTopC
      case ( FOLBottomC, r )     => r
      case ( r, FOLBottomC )     => r
      case ( l, r ) if l == r => l
      case ( l, r )           => FOLOr( l, r )
    }
    case FOLImp( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( FOLTopC, r )        => r
      case ( _, FOLTopC )        => FOLTopC
      case ( FOLBottomC, _ )     => FOLTopC
      case ( r, FOLBottomC )     => simplify( FOLNeg( r ) )
      case ( l, r ) if l == r => FOLTopC
      case ( l, r )           => FOLImp( l, r )
    }
    case FOLNeg( s ) => simplify( s ) match {
      case FOLTopC    => FOLBottomC
      case FOLBottomC => FOLTopC
      case s       => FOLNeg( s )
    }
    case _ => f
  }
}
