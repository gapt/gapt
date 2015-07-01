/*
 * Wrapper function for substitutions in FOL.
 *
 **/

package at.logic.gapt.expr.fol

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.FSequent

import scala.collection.GenTraversable

class FOLSubstitution( val folmap: Map[FOLVar, FOLTerm] ) extends Substitution( folmap.asInstanceOf[Map[Var, LambdaExpression]] ) {
  def apply( t: FOLTerm ): FOLTerm = super.apply( t ).asInstanceOf[FOLTerm]
  def apply( t: FOLFormula ): FOLFormula = super.apply( t ).asInstanceOf[FOLFormula]
  def apply( t: FOLExpression ): FOLExpression = super.apply( t ).asInstanceOf[FOLExpression]

  def compose( sub: FOLSubstitution ): FOLSubstitution = FOLSubstitution( folmap ++ sub.folmap.map( x => ( x._1, apply( x._2 ) ) ) )
}
object FOLSubstitution {
  def apply( subs: GenTraversable[( FOLVar, FOLTerm )] ): FOLSubstitution = new FOLSubstitution( Map() ++ subs )
  def apply( subs: ( FOLVar, FOLTerm )* ): FOLSubstitution = new FOLSubstitution( Map() ++ subs )
  def apply( variable: FOLVar, term: FOLTerm ): FOLSubstitution = new FOLSubstitution( Map( variable -> term ) )
  def apply( map: Map[FOLVar, FOLTerm] ): FOLSubstitution = new FOLSubstitution( map )
  def apply() = new FOLSubstitution( Map() )
}

