/*
 * SubsumptionAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
import at.logic.calculi.lk.base._

trait SubsumptionAlgorithm {
  def subsumes(s1: Sequent, s2: Sequent): Boolean
}
