/*
 * SimpleManager.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption.managers

import at.logic.calculi.lk.base._
import at.logic.utils.ds.PublishingBuffer

class SimpleManager(pb: PublishingBuffer[Sequent], alg: SubsumptionAlgorithm) extends SubsumptionManager {
  val sequents = pb
  val sbsmpAlg = alg
  protected def addSequent(s: Sequent) = ()
  protected def removeSequent(s: Sequent) = ()

  def forwardSubsumption(s: Sequent) = sequents.exists(s2 => sbsmpAlg.subsumes(s2, s))
  def backwardSubsumption(s: Sequent) = sequents.toList.foreach(s2 => if (sbsmpAlg.subsumes(s, s2)) sequents -= s2)
}
