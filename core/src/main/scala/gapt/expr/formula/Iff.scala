package gapt.expr.formula

import gapt.expr.Expr

object Iff {
  def apply( a: Expr, b: Expr ): Formula = And( Imp( a, b ), Imp( b, a ) )
  def unapply( f: Formula ): Option[( Formula, Formula )] =
    f match {
      case And( Imp( a, b ), Imp( b_, a_ ) ) if a == a_ && b == b_ => Some( ( a, b ) )
      case _ => None
    }
}
