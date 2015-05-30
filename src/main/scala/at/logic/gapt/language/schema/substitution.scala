/*
 * Wrapper function for substitutions in Schema.
 *
 **/

package at.logic.gapt.language.schema

import at.logic.gapt.expr._
import at.logic.gapt.language.hol.HOLSubstitution

class SchemaSubstitution( val schemamap: Map[Var, SchemaExpression] ) extends HOLSubstitution( schemamap.asInstanceOf[Map[Var, LambdaExpression]] )
object SchemaSubstitution {
  def apply( subs: List[( Var, SchemaExpression )] ): SchemaSubstitution = new SchemaSubstitution( Map() ++ subs )
  def apply( variable: Var, expression: SchemaExpression ): SchemaSubstitution = new SchemaSubstitution( Map( variable -> expression ) )
  def apply( map: Map[Var, SchemaExpression] ): SchemaSubstitution = new SchemaSubstitution( map )
  def apply() = new SchemaSubstitution( Map() )
}

