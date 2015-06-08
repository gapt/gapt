/*
 * Wrapper function for substitutions in Schema.
 *
 **/

package at.logic.gapt.expr.schema

import at.logic.gapt.expr._

class SchemaSubstitution( val schemamap: Map[Var, SchemaExpression] ) extends Substitution( schemamap.asInstanceOf[Map[Var, LambdaExpression]] )
object SchemaSubstitution {
  def apply( subs: List[( Var, SchemaExpression )] ): SchemaSubstitution = new SchemaSubstitution( Map() ++ subs )
  def apply( variable: Var, expression: SchemaExpression ): SchemaSubstitution = new SchemaSubstitution( Map( variable -> expression ) )
  def apply( map: Map[Var, SchemaExpression] ): SchemaSubstitution = new SchemaSubstitution( map )
  def apply() = new SchemaSubstitution( Map() )
}

