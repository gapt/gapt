/*
 * SubsumptionAlgorithm.scala
 *
 */

package at.logic.algorithms.subsumption

import at.logic.calculi.lk.base.FSequent

trait SubsumptionAlgorithm {
  def subsumes(s1: FSequent, s2: FSequent): Boolean
}
