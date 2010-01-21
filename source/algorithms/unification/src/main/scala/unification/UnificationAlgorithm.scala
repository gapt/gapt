/*
 * UnificationAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.unification

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._

trait UnificationAlgorithm {
  def unifiy(term1: LambdaExpression, term2: LambdaExpression): Option[Substitution]
}
