/*
 * MatchingAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.matching

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._

// the restrictedDomain is a list of variables that should not be included in the substitution.
// i.e. these are variables contained on the right hand side of an object (clause, sequent, etc.) that contains the lambda expression to be matched
trait MatchingAlgorithm {
  def matchTerm(term: LambdaExpression, posInstance: LambdaExpression, restrictedDomain: List[Var]): Option[Substitution[LambdaExpression]]
}