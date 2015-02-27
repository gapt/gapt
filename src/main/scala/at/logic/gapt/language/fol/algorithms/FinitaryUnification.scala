package at.logic.gapt.language.fol.algorithms

import at.logic.gapt.language.fol.{ FOLExpression, FOLSubstitution }

/**
 * The interface for an unification algorithm of finitary type, i.e.
 * one where the complete set of most general unifiers is finite.
 */
trait FinitaryUnification {
  /**
   * Calculates the complete set of most general unifiers of the terms term1 and term2.
   * @param term1 one of the terms to unify. formulas are also allowed, so we accept FOL expressions
   * @param term2 one of the terms to unify. formulas are also allowed, so we accept FOL expressions
   * @return a list of mgus, the empty list means that term1 and term2 are not unifiable.
   */
  def unify( term1: FOLExpression, term2: FOLExpression ): List[FOLSubstitution]
}
