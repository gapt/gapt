package at.logic.gapt.models

import at.logic.gapt.expr._

/* A trait describing propositional interpretations */
trait Interpretation {
  // Interpret an atom.
  def interpretAtom( atom: HOLFormula ): Boolean

  // Interpret an arbitrary formula.
  def interpret( f: HOLFormula ): Boolean = f match {
    case And( f1, f2 )   => interpret( f1 ) && interpret( f2 )
    case Or( f1, f2 )    => interpret( f1 ) || interpret( f2 )
    case Imp( f1, f2 )   => !interpret( f1 ) || interpret( f2 )
    case Neg( f1 )       => !interpret( f1 )
    case HOLAtom( _, _ ) => interpretAtom( f )
  }

}

class MapBasedInterpretation( val model: Map[HOLFormula, Boolean] ) extends Interpretation {
  def interpretAtom( atom: HOLFormula ) = model.get( atom ) match {
    case Some( b ) => b
    case None      => false
  }

  override def toString = {
    model.foldLeft( "" ) { case ( s, ( atom, value ) ) => s + atom + " -> " + value + "\n" }
  }
}
