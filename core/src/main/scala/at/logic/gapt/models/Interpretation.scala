package at.logic.gapt.models

import at.logic.gapt.expr._

/* A trait describing propositional interpretations */
trait Interpretation {
  // Interpret an atom.
  def interpretAtom( atom: HOLAtom ): Boolean

  // Interpret an arbitrary formula.
  def interpret( f: HOLFormula ): Boolean = f match {
    case And( f1, f2 ) => interpret( f1 ) && interpret( f2 )
    case Or( f1, f2 )  => interpret( f1 ) || interpret( f2 )
    case Imp( f1, f2 ) => !interpret( f1 ) || interpret( f2 )
    case Neg( f1 )     => !interpret( f1 )
    case Bottom()      => false
    case Top()         => true
    case f: HOLAtom    => interpretAtom( f )
  }

}

case class MapBasedInterpretation( model: Map[HOLAtom, Boolean] ) extends Interpretation {
  def interpretAtom( atom: HOLAtom ) = model.getOrElse( atom, false )

  override def toString = model.toSeq.
    map { case ( atom, value ) => s"$atom -> $value" }.
    sorted.mkString( sys.props( "line.separator" ) )
}
