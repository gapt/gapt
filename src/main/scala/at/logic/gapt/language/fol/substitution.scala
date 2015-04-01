/*
 * Wrapper function for substitutions in FOL.
 *
 **/

package at.logic.gapt.language.fol

import at.logic.gapt.language.hol.{ HOLSubstitution, HOLExpression, HOLVar }

class FOLSubstitution( val folmap: Map[FOLVar, FOLExpression] ) extends HOLSubstitution( folmap.asInstanceOf[Map[HOLVar, HOLExpression]] ) {
  def apply( t: FOLExpression ): FOLExpression = {
    val s = HOLSubstitution( map.asInstanceOf[Map[HOLVar, HOLExpression]] )
    s( t ).asInstanceOf[FOLExpression]
  }
  def apply( t: FOLFormula ): FOLFormula = {
    val s = HOLSubstitution( map.asInstanceOf[Map[HOLVar, HOLExpression]] )
    s( t ).asInstanceOf[FOLFormula]
  }
  def apply( t: FOLTerm ): FOLTerm = {
    val s = HOLSubstitution( map.asInstanceOf[Map[HOLVar, HOLExpression]] )
    s( t ).asInstanceOf[FOLTerm]
  }

  def compose( sub: FOLSubstitution ): FOLSubstitution = FOLSubstitution( folmap ++ sub.folmap.map( x => ( x._1, apply( x._2 ) ) ) )
}
object FOLSubstitution {
  def apply( subs: Seq[( FOLVar, FOLExpression )] ): FOLSubstitution = new FOLSubstitution( Map() ++ subs )
  def apply( sub: ( FOLVar, FOLExpression ), subs: ( FOLVar, FOLExpression )* ): FOLSubstitution = new FOLSubstitution( Map( sub ) ++ subs )
  def apply( variable: FOLVar, expression: FOLExpression ): FOLSubstitution = new FOLSubstitution( Map( variable -> expression ) )
  def apply( map: Map[FOLVar, FOLExpression] ): FOLSubstitution = new FOLSubstitution( map )
  def apply() = new FOLSubstitution( Map() )
}

