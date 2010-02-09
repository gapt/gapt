/*
 * SubsumptionAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._

trait SubsumptionAlgorithm {
  def subsumes(ls1: Tuple2[List[LambdaExpression], List[LambdaExpression]], ls2: Tuple2[List[LambdaExpression], List[LambdaExpression]]): Boolean
}
