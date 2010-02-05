/*
 * UnificationBasedFOLMatchingAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.matching.fol

import at.logic.algorithms.matching.MatchingAlgorithm
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm

object UnificationBasedFOLMatchingAlgorithm extends MatchingAlgorithm {
  def matchTerm(term: LambdaExpression, posInstance: LambdaExpression): Option[Substitution] = FOLUnificationAlgorithm.unify(term, posInstance) match {
    case s @ Some(sub) if (sub(posInstance) == posInstance) => s // i.e. the substitution is applicable only on term
    case _ => None
  }
}
