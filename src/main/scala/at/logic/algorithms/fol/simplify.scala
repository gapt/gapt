package at.logic.algorithms.fol.simplify

import at.logic.language.fol._

// TODO: this is copy'n'paste from HOL; done since the 
// logical constants in HOL/FOL are different. Reimplement
// this on top of the HOL algorithm once the superflous
// copies of the logical constants have been deleted by
// refactoring.
object simplify {
  def apply( f: FOLFormula ): FOLFormula = f match {
    case And( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( TopC, r )        => r
      case ( r, TopC )        => r
      case ( BottomC, _ )     => BottomC
      case ( _, BottomC )     => BottomC
      case ( l, r ) if l == r => l
      case ( l, r )           => And( l, r )
    }
    case Or( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( TopC, _ )        => TopC
      case ( _, TopC )        => TopC
      case ( BottomC, r )     => r
      case ( r, BottomC )     => r
      case ( l, r ) if l == r => l
      case ( l, r )           => Or( l, r )
    }
    case Imp( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( TopC, r )        => r
      case ( _, TopC )        => TopC
      case ( BottomC, _ )     => TopC
      case ( r, BottomC )     => simplify( Neg( r ) )
      case ( l, r ) if l == r => TopC
      case ( l, r )           => Imp( l, r )
    }
    case Neg( s ) => simplify( s ) match {
      case TopC    => BottomC
      case BottomC => TopC
      case s       => Neg( s )
    }
    case _ => f
  }
}
