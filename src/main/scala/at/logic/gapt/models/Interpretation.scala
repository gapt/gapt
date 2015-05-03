package at.logic.gapt.models

import at.logic.gapt.expr._

/* A trait describing propositional interpretations */
trait Interpretation {
  // Interpret an atom.
  def interpretAtom( atom: Formula ): Boolean

  // Interpret an arbitrary formula.
  def interpret( f: Formula ): Boolean = f match {
    case And( f1, f2 )   => interpret( f1 ) && interpret( f2 )
    case Or( f1, f2 )    => interpret( f1 ) || interpret( f2 )
    case Imp( f1, f2 )   => !interpret( f1 ) || interpret( f2 )
    case Neg( f1 )       => !interpret( f1 )
    case HOLAtom( _, _ ) => interpretAtom( f )
  }

}

class MapBasedInterpretation( val model: Map[Formula, Boolean] ) extends Interpretation {
  def interpretAtom( atom: Formula ) = model.get( atom ) match {
    case Some( b ) => b
    case None      => false
  }

  override def toString = {
    model.foldLeft( "" ) { case ( s, ( atom, value ) ) => s + atom + " -> " + value + "\n" }
  }
}
