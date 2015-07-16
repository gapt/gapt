/*
 * SubsumptionAlgorithm.scala
 *
 */

package at.logic.gapt.proofs.lk.subsumption

import at.logic.gapt.proofs.lk.base.HOLSequent

trait SubsumptionAlgorithm {
  /**
   * A predicate which is true iff s2 is subsumed by s1.
   * @param s1 a clause
   * @param s2 a clause
   * @return true iff s1 subsumes s2
   */
  def subsumes( s1: HOLSequent, s2: HOLSequent ): Boolean
}
