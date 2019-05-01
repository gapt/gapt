package gapt.logic

import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.fol.FOLFormula

object toImplications {
  /**
   * Transforms subformulas of the form ¬A ∨ B or A ∨ ¬B to A → B or B → A, respectively.
   *
   * @param formula
   * @return
   */
  def apply( formula: Formula ): Formula = formula match {
    case Or( Neg( f ), g ) =>
      Imp( apply( f ), apply( g ) )
    case Or( f, Neg( g ) ) =>
      Imp( apply( g ), apply( f ) )
    case Or( f, g ) =>
      Or( apply( f ), apply( g ) )
    case And( f, g ) =>
      And( apply( f ), apply( g ) )
    case Neg( f )    => Neg( apply( f ) )
    case Ex( v, f )  => Ex( v, apply( f ) )
    case All( v, f ) => All( v, apply( f ) )
    case _           => formula
  }

  def apply( formula: FOLFormula ): FOLFormula = apply( formula.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]
}
