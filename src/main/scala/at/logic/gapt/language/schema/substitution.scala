/*
 * Wrapper function for substitutions in Schema.
 *
 **/

package at.logic.gapt.language.schema

import at.logic.gapt.language.hol.{ HOLSubstitution => SubstitutionHOL, HOLExpression, HOLVar }

class SchemaSubstitution( val schemamap: Map[SchemaVar, SchemaExpression] ) extends SubstitutionHOL( schemamap.asInstanceOf[Map[HOLVar, HOLExpression]] ) {
  def apply( t: SchemaExpression ): SchemaExpression = {
    val s = SubstitutionHOL( map.asInstanceOf[Map[HOLVar, HOLExpression]] )
    s( t ).asInstanceOf[SchemaExpression]
  }
  def apply( t: SchemaFormula ): SchemaFormula = {
    val s = SubstitutionHOL( map.asInstanceOf[Map[HOLVar, HOLExpression]] )
    s( t ).asInstanceOf[SchemaFormula]
  }
}
object SchemaSubstitution {
  def apply( subs: List[( SchemaVar, SchemaExpression )] ): SchemaSubstitution = new SchemaSubstitution( Map() ++ subs )
  def apply( variable: SchemaVar, expression: SchemaExpression ): SchemaSubstitution = new SchemaSubstitution( Map( variable -> expression ) )
  def apply( map: Map[SchemaVar, SchemaExpression] ): SchemaSubstitution = new SchemaSubstitution( map )
  def apply() = new SchemaSubstitution( Map() )
}

