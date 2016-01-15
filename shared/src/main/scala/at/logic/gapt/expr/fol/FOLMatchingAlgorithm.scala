package at.logic.gapt.expr.fol

import at.logic.gapt.expr._

object FOLMatchingAlgorithm {
  /**
   * Computes a FOLSubstitution that turns term from into term to, if one exists.
   *
   * @param from A LambdaExpression.
   * @param to A LambdaExpression.
   * @param forbiddenVars A set of variables that cannot be in the domain of the FOLSubstitution. Defaults to the empty set.
   * @return If there is a variable FOLSubstitution that turns from into to And doesn't contain any elements of forbiddenVars, it is returned. Otherwise None.
   */
  def matchTerms( from: FOLExpression, to: FOLExpression, forbiddenVars: Set[FOLVar] = Set() ): Option[FOLSubstitution] =
    syntacticMatching( List( from -> to ), forbiddenVars map { v => v -> v } toMap )

  def matchTerms( pairs: List[( FOLExpression, FOLExpression )] ): Option[FOLSubstitution] =
    syntacticMatching( pairs )
}
