/*
 * SimpleManager.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption.managers

import at.logic.algorithms.subsumption._
import at.logic.calculi.lk.base._
import at.logic.utils.ds.PublishingBuffer
import at.logic.calculi.lk.base.types._

class SimpleManager(pb: PublishingBuffer[FSequent], alg: SubsumptionAlgorithm) extends SubsumptionManager {
  val sequents = pb
  val sbsmpAlg = alg
  init
  protected def addSequent(s: FSequent) = ()
  protected def removeSequent(s: FSequent) = ()

  def forwardSubsumption(s: FSequent) = sequents.exists(s2 => sbsmpAlg.subsumes(s2, s))
  def backwardSubsumption(s: FSequent) = sequents.toList.foreach(s2 => if (sbsmpAlg.subsumes(s, s2)) sequents -= s2)
}
