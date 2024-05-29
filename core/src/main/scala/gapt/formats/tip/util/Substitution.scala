package gapt.formats.tip.util

import gapt.formats.tip.parser.TipSmtExpression
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtProblem

case class Substitution(map: (TipSmtIdentifier, TipSmtExpression)*) {

  private val substitution = Map(map: _*)

  /**
   * Creates a new substitution.
   *
   * @param variable A variable with which a term is to be associated.
   * @param term A term to be associated with the given variable.
   * @return
   */
  def this(variable: TipSmtIdentifier, term: TipSmtExpression) = {
    this(variable -> term)
  }

  /**
   * Filters the variable/term associations.
   *
   * @param predicate The predicate that is used to filter the substitution.
   * @return A substitution containing only those variable/term associations
   * for which the predicate has evaluated to true.
   */
  def filter(
      predicate: (TipSmtIdentifier, TipSmtExpression) => Boolean
  ) //
      : Substitution = {
    Substitution(
      substitution.filter { case (v, t) => predicate(v, t) } toSeq: _*
    )
  }

  /**
   * @return The set variables for which this substitution is defined.
   */
  def domain: Set[TipSmtIdentifier] = {
    substitution.keySet
  }

  /**
   * Retrieves the free variables of the expressions in this subsitutition.
   *
   * @param problem The problem with respect to which free variables are
   * determined.
   * @return The set of all free variables occurring the expressions of
   * this substitution
   */
  def range(implicit problem: TipSmtProblem): Set[TipSmtIdentifier] = {
    substitution
      .values
      .flatMap { freeVariables(problem, _) }
      .toSet
      .map { TipSmtIdentifier(_) }
  }

  /**
   * Retrieves the term associated with the given variable.
   *
   * @param variable The variable whose associated term is to be retrieved.
   * @return The associated term if it exists, otherwise the variable is
   * returned unmodified.
   */
  def get(variable: TipSmtIdentifier): TipSmtExpression = {
    substitution.getOrElse(variable, variable)
  }
}
