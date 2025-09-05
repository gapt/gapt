package gapt.expr

import gapt.expr.formula.Formula
import gapt.expr.subst.Substitution
import gapt.expr.subst.FOLSubstitution
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.subst.Substitutable

/**
* Trait that captures the creation of a substitution from a map of variables to terms
*/
trait SubstitutionFromMap[S <: Substitution, V, T] {
  def createFromMap(map: Map[V, T]): S
}

given SubstitutionFromMap[FOLSubstitution, FOLVar, FOLTerm] = (map: Map[FOLVar, FOLTerm]) => new FOLSubstitution(map)
given SubstitutionFromMap[Substitution, Var, Expr] = (map: Map[Var, Expr]) => new Substitution(map)

extension [S <: Substitution, T, U](t: T)(using substitutable: Substitutable[S, T, U])
  /**
  * Convenience method to apply a substitution to a term/formula/expression as a post-fix operation
  */
  def applySubstitution(s: S): U = substitutable.applySubstitution(s, t)

extension [S <: Substitution, T, V, E, U](t: T)(using Substitutable[S, T, U])(using creationOps: SubstitutionFromMap[S, V, E])
  /**
  * Convenience method to apply a substitution given as a map to a given term/formula/expression as a post-fix operation
  */
  def substitute(map: Map[V, E]) = t.applySubstitution(creationOps.createFromMap(map))

  /**
  * Convenience method to apply a substitution given as an iterable of variable-term pairs to terms to a given term/formula/expression as a post-fix operation
  */
  def substitute(subs: Iterable[(V, E)]) = t.applySubstitution(creationOps.createFromMap(Map() ++ subs))

  /**
  * Convenience method to apply a substitution given as a sequence of variable-term pairs to a given term/formula/expression as a post-fix operation
  */
  def substitute(subs: (V, E)*) = t.applySubstitution(creationOps.createFromMap(Map() ++ subs))
