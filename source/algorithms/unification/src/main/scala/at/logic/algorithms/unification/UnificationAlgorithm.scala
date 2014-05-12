/*
 * UnificationAlgorithm.scala
 *
 */

package at.logic.algorithms.unification

import at.logic.language.fol.FOLExpression
import at.logic.language.fol.Substitution

trait FinitaryUnification {
  def unify(term1:FOLExpression, term2:FOLExpression) : List[Substitution]
}

trait UnificationAlgorithm extends FinitaryUnification
