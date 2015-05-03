/*
 * Wrapper function for substitutions in FOL.
 *
 **/

package at.logic.gapt.language.fol

import at.logic.gapt.expr._
import at.logic.gapt.language.hol.HOLSubstitution

// FIXME: does FOLExpression really make sense here (instead of FOLTerm)?

class FOLSubstitution( val folmap: Map[FOLVar, FOLExpression] ) extends HOLSubstitution( folmap.asInstanceOf[Map[Var, LambdaExpression]] ) {
  def apply( t: FOLTerm ): FOLTerm = {
    val s = HOLSubstitution( map.asInstanceOf[Map[Var, LambdaExpression]] )
    s( t ).asInstanceOf[FOLTerm]
  }
  def apply( t: FOLFormula ): FOLFormula = {
    val s = HOLSubstitution( map.asInstanceOf[Map[Var, LambdaExpression]] )
    s( t ).asInstanceOf[FOLFormula]
  }
  def apply( t: FOLExpression ): FOLExpression = {
    val s = HOLSubstitution( map.asInstanceOf[Map[Var, LambdaExpression]] )
    s( t ).asInstanceOf[FOLExpression]
  }

  def compose( sub: FOLSubstitution ): FOLSubstitution = FOLSubstitution( folmap ++ sub.folmap.map( x => ( x._1, apply( x._2 ) ) ) )
}
object FOLSubstitution {
  def apply( subs: List[( FOLVar, FOLExpression )] ): FOLSubstitution = new FOLSubstitution( Map() ++ subs )
  def apply( variable: FOLVar, expression: FOLExpression ): FOLSubstitution = new FOLSubstitution( Map( variable -> expression ) )
  def apply( map: Map[FOLVar, FOLExpression] ): FOLSubstitution = new FOLSubstitution( map )
  def apply() = new FOLSubstitution( Map() )
}

