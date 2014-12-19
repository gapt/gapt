/*
 * Wrapper function for substitutions in FOL.
 *
 **/

package at.logic.language.fol

import at.logic.language.hol.{Substitution => SubstitutionHOL, HOLExpression, HOLVar}

class Substitution(val folmap: Map[FOLVar, FOLExpression]) extends SubstitutionHOL(folmap.asInstanceOf[Map[HOLVar, HOLExpression]]) {
  def apply(t: FOLExpression): FOLExpression = {
    val s = SubstitutionHOL(map.asInstanceOf[Map[HOLVar, HOLExpression]])
    s(t).asInstanceOf[FOLExpression]
  }
  def apply(t: FOLFormula): FOLFormula = {
    val s = SubstitutionHOL(map.asInstanceOf[Map[HOLVar, HOLExpression]])
    s(t).asInstanceOf[FOLFormula]
  }
  def apply(t: FOLTerm): FOLTerm = {
    val s = SubstitutionHOL(map.asInstanceOf[Map[HOLVar, HOLExpression]])
    s(t).asInstanceOf[FOLTerm]
  }
  
  def compose(sub: Substitution): Substitution = Substitution(folmap ++ sub.folmap.map(x => (x._1, apply(x._2))))
}
object Substitution {
  def apply(subs: List[(FOLVar, FOLExpression)]): Substitution = new Substitution(Map() ++ subs)
  def apply(variable: FOLVar, expression: FOLExpression): Substitution = new Substitution(Map(variable -> expression))
  def apply(map: Map[FOLVar, FOLExpression]): Substitution = new Substitution( map )
  def apply() = new Substitution(Map())
}

