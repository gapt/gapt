package gapt.expr.formula

import gapt.expr.Expr
import gapt.expr.formula.fol.FOLFormula

object Iff {

  def apply( a: Expr, b: Expr ): Formula = And( Imp( a, b ), Imp( b, a ) )

  /**
   * Constructs a first-order biconditional.
   *
   * @param a
   * @param b
   * @return The returned formula is `(a -> b) & (b -> a)`.
   */
  def apply( a: FOLFormula, b: FOLFormula ): FOLFormula =
    Iff( a.asInstanceOf[Expr], b ).asInstanceOf[FOLFormula]

  def unapply( f: Formula ): Option[( Formula, Formula )] =
    f match {
      case And( Imp( a, b ), Imp( b_, a_ ) ) if a == a_ && b == b_ => Some( ( a, b ) )
      case _ => None
    }
}
