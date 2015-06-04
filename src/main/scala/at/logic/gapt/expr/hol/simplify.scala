package at.logic.gapt.expr.hol.simplify

import at.logic.gapt.expr._

object simplify {
  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]
  def apply( f: HOLFormula ): HOLFormula = f match {
    case And( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( Top(), r )       => r
      case ( r, Top() )       => r
      case ( Bottom(), _ )    => Bottom()
      case ( _, Bottom() )    => Bottom()
      case ( l, r ) if l == r => l
      case ( l, r )           => And( l, r )
    }
    case Or( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( Top(), _ )       => Top()
      case ( _, Top() )       => Top()
      case ( Bottom(), r )    => r
      case ( r, Bottom() )    => r
      case ( l, r ) if l == r => l
      case ( l, r )           => Or( l, r )
    }
    case Imp( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( Top(), r )       => r
      case ( _, Top() )       => Top()
      case ( Bottom(), _ )    => Top()
      case ( r, Bottom() )    => simplify( Neg( r ) )
      case ( l, r ) if l == r => Top()
      case ( l, r )           => Imp( l, r )
    }
    case Neg( s ) => simplify( s ) match {
      case Top()    => Bottom()
      case Bottom() => Top()
      case s        => Neg( s )
    }
    case _ => f
  }
}
