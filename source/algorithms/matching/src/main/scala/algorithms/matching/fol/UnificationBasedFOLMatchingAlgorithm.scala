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

object UnificationBasedFOLMatchingAlgorithm extends MatchingAlgorithm {
  def matchTerm(term: LambdaExpression, posInstance: LambdaExpression): Option[Substitution] = FOLMatchingAlgorithm.matchTerm(term, posInstance)
}
