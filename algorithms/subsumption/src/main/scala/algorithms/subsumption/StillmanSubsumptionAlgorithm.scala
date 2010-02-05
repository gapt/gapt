/*
 * StillmanSubsumptionAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption

import at.logic.algorithms.matching.MatchingAlgorithm
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.symbols._

trait StillmanSubsumptionAlgorithm extends SubsumptionAlgorithm {
  val matchAlg: MatchingAlgorithm
  def subsumes(ls1: List[LambdaExpression], ls2: List[LambdaExpression]): Boolean = ST(ls1, ls2, Substitution())

  def ST(ls1: List[LambdaExpression], ls2: List[LambdaExpression], sub: LambdaExpression => LambdaExpression): Boolean = ls1 match {
    case Nil => true // first list is exhausted
    case x::ls => val sx = sub(x); ls2.exists(t => matchAlg.matchTerm(sx, t) match {
      case Some(sub2) => ST(ls, ls2, sub2 compose sub)
      case None => false
    })
  }
}
