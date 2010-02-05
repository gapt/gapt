/*
 * MatchingAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.matching

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._

trait MatchingAlgorithm {
  def matchTerm(term: LambdaExpression, posInstance: LambdaExpression): Option[Substitution]
}