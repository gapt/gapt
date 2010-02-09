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
import at.logic.language.hol.propositions._

trait StillmanSubsumptionAlgorithm extends SubsumptionAlgorithm {
  val matchAlg: MatchingAlgorithm
  def subsumes(ls1: Tuple2[List[LambdaExpression], List[LambdaExpression]], ls2: Tuple2[List[LambdaExpression], List[LambdaExpression]]): Boolean = 
    ST(ls1._1.map(x => Neg(x.asInstanceOf[Formula])) ++ ls1._2, ls2._1.map(x => Neg(x.asInstanceOf[Formula])) ++ ls2._2, Substitution())


  def ST(ls1: List[LambdaExpression], ls2: List[LambdaExpression], sub: LambdaExpression => LambdaExpression): Boolean = ls1 match {
    case Nil => true // first list is exhausted
    case x::ls => val sx = sub(x); ls2.exists(t => matchAlg.matchTerm(sx, t) match {
      case Some(sub2) if ls2.forall(el => sub2(el) == el) => ST(ls, ls2, sub2 compose sub) // the condition ensures that the match did not replace variables in the "ground" term
      case _ => false
    })
  }
}
