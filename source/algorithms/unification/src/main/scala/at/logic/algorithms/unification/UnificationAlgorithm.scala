/*
 * UnificationAlgorithm.scala
 *
 */

package at.logic.algorithms.unification

import at.logic.language.fol.FOLExpression
import at.logic.language.fol.Substitution

/**
 * The interface for an unification algorithm of finitary type, i.e.
 * one where the complete set of most general unifiers is finite.
 */
trait FinitaryUnification {
  /**
   * Calculates the complete set of most general unifiers of the terms term1 and term2.
   * @param term1 one of the terms to unify. formulas are also allowed, so we accept FOL expressions
   * @param term2 one of the terms to unify. formulas are also allowed, so we accept FOL expressions
   * @return a list of mgus
   */
  def unify(term1:FOLExpression, term2:FOLExpression) : List[Substitution]
}

trait UnificationAlgorithm extends FinitaryUnification
