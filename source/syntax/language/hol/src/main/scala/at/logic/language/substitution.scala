/*
 * Wrapper function for substitutions in HOL.
 *
 **/

package at.logic.language.hol

import at.logic.language.lambda.{Substitution => SubstitutionLambda, LambdaExpression, Var}

class Substitution(val holmap: Map[HOLVar, HOLExpression]) extends SubstitutionLambda(holmap.asInstanceOf[Map[Var, LambdaExpression]]) {
  def apply(t: HOLExpression): HOLExpression = {
    val s = SubstitutionLambda(map.asInstanceOf[Map[Var, LambdaExpression]])
    s(t).asInstanceOf[HOLExpression]
  }
  def apply(t: HOLFormula): HOLFormula = {
    val s = SubstitutionLambda(map.asInstanceOf[Map[Var, LambdaExpression]])
    s(t).asInstanceOf[HOLFormula]
  }
  
  def compose(sub: Substitution): Substitution = Substitution(holmap ++ sub.holmap.map(x => (x._1, apply(x._2))))

}
object Substitution {
  def apply(subs: List[(HOLVar, HOLExpression)]): Substitution = new Substitution(Map() ++ subs)
  def apply(variable: HOLVar, expression: HOLExpression): Substitution = new Substitution(Map(variable -> expression))
  def apply(map: Map[HOLVar, HOLExpression]): Substitution = new Substitution( map )
  def apply() = new Substitution(Map())
}