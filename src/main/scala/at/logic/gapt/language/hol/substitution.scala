/*
 * Wrapper function for substitutions in HOL.
 *
 **/

package at.logic.gapt.language.hol

import at.logic.gapt.language.lambda.{ LambdaExpression, Var, LambdaSubstitution }

class HOLSubstitution( val holmap: Map[HOLVar, HOLExpression] ) extends LambdaSubstitution( holmap.asInstanceOf[Map[Var, LambdaExpression]] ) {
  def apply( t: HOLExpression ): HOLExpression = {
    val s = LambdaSubstitution( map.asInstanceOf[Map[Var, LambdaExpression]] )
    s( t ).asInstanceOf[HOLExpression]
  }
  def apply( t: HOLFormula ): HOLFormula = {
    val s = LambdaSubstitution( map.asInstanceOf[Map[Var, LambdaExpression]] )
    s( t ).asInstanceOf[HOLFormula]
  }

  def compose( sub: HOLSubstitution ): HOLSubstitution = HOLSubstitution( holmap ++ sub.holmap.map( x => ( x._1, apply( x._2 ) ) ) )

}
object HOLSubstitution {
  def apply( subs: List[( HOLVar, HOLExpression )] ): HOLSubstitution = new HOLSubstitution( Map() ++ subs )
  def apply( variable: HOLVar, expression: HOLExpression ): HOLSubstitution = new HOLSubstitution( Map( variable -> expression ) )
  def apply( map: Map[HOLVar, HOLExpression] ): HOLSubstitution = new HOLSubstitution( map )
  def apply() = new HOLSubstitution( Map() )
}