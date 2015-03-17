package at.logic.algorithms.hol.simplify

import at.logic.language.hol._

object simplify {
  def apply( f: HOLFormula ): HOLFormula = f match {
    case And( l, r ) => (simplify( l ), simplify( r )) match {
        case (TopC, r) => r
        case (r, TopC) => r
        case (BottomC, _) => BottomC
        case (_, BottomC) => BottomC
        case (l, r) => And( l, r )
      }
    case Or( l, r ) => (simplify( l ), simplify( r )) match {
        case (TopC, _) => TopC
        case (_, TopC) => TopC
        case (BottomC, r) => r
        case (r, BottomC) => r
        case (l, r) => Or( l, r )
      }
    case Imp( l, r ) => (simplify( l ), simplify( r )) match {
        case (TopC, r) => r
        case (_, TopC) => TopC
        case (BottomC, _) => TopC
        case (r, BottomC) => simplify( Neg( r ) )
        case (l, r) => Imp( l, r )
      }
    case Neg( s ) => simplify(s) match {
      case TopC => BottomC
      case BottomC => TopC
      case s => Neg( s )
    }
    case _ => f
  }
}
