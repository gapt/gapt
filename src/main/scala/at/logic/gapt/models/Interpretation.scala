package at.logic.gapt.models

import at.logic.gapt.language.hol._

/* A trait describing propositional interpretations */
trait Interpretation {
  // Interpret an atom.
  def interpretAtom( atom: HOLFormula ): Boolean

  // Interpret an arbitrary formula.
  def interpret( f: HOLFormula ): Boolean = f match {
    case HOLAnd( f1, f2 ) => interpret( f1 ) && interpret( f2 )
    case HOLOr( f1, f2 )  => interpret( f1 ) || interpret( f2 )
    case HOLImp( f1, f2 ) => !interpret( f1 ) || interpret( f2 )
    case HOLNeg( f1 )     => !interpret( f1 )
    case HOLAtom( _, _ )  => interpretAtom( f )
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
