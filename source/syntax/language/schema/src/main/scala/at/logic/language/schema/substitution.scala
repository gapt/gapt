/*
 * Wrapper function for substitutions in Schema.
 *
 **/

package at.logic.language.schema

import at.logic.language.hol.{Substitution => SubstitutionHOL, HOLExpression, HOLVar}

class Substitution(val schemamap: Map[SchemaVar, SchemaExpression]) extends SubstitutionHOL(schemamap.asInstanceOf[Map[HOLVar, HOLExpression]]) {
  def apply(t: SchemaExpression): SchemaExpression = {
    val s = SubstitutionHOL(map.asInstanceOf[Map[HOLVar, HOLExpression]])
    s(t).asInstanceOf[SchemaExpression]
  }
  def apply(t: SchemaFormula): SchemaFormula = {
    val s = SubstitutionHOL(map.asInstanceOf[Map[HOLVar, HOLExpression]])
    s(t).asInstanceOf[SchemaFormula]
  }
}
object Substitution {
  def apply(subs: List[(SchemaVar, SchemaExpression)]): Substitution = new Substitution(Map() ++ subs)
  def apply(variable: SchemaVar, expression: SchemaExpression): Substitution = new Substitution(Map(variable -> expression))
  def apply(map: Map[SchemaVar, SchemaExpression]): Substitution = new Substitution( map )
  def apply() = new Substitution(Map())
}

