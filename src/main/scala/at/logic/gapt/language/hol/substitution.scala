/*
 * Wrapper function for substitutions in HOL.
 *
 **/

package at.logic.gapt.language.hol

import at.logic.gapt.expr._

@deprecated
class HOLSubstitution( val holmap: Map[Var, LambdaExpression] ) extends LambdaSubstitution( holmap.asInstanceOf[Map[Var, LambdaExpression]] ) {
  def apply( t: Formula ): Formula = {
    val s = LambdaSubstitution( map.asInstanceOf[Map[Var, LambdaExpression]] )
    s( t ).asInstanceOf[Formula]
  }

  def compose( sub: HOLSubstitution ): HOLSubstitution = HOLSubstitution( holmap ++ sub.holmap.map( x => ( x._1, apply( x._2 ) ) ) )

}
@deprecated
object HOLSubstitution {
  def apply( subs: List[( Var, LambdaExpression )] ): HOLSubstitution = new HOLSubstitution( Map() ++ subs )
  def apply( variable: Var, expression: LambdaExpression ): HOLSubstitution = new HOLSubstitution( Map( variable -> expression ) )
  def apply( map: Map[Var, LambdaExpression] ): HOLSubstitution = new HOLSubstitution( map )
  def apply() = new HOLSubstitution( Map() )
}