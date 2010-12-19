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

class SimpleManager(pb: PublishingBuffer[SequentLike], alg: SubsumptionAlgorithm) extends SubsumptionManager {
  val sequents = pb
  val sbsmpAlg = alg
  init
  protected def addSequent(s: SequentLike) = ()
  protected def removeSequent(s: SequentLike) = ()

  def forwardSubsumption(s: SequentLike) = sequents.exists(s2 => sbsmpAlg.subsumes(s2.getSequent, s.getSequent))
  def backwardSubsumption(s: SequentLike) = sequents.toList.foreach(s2 => if (sbsmpAlg.subsumes(s.getSequent, s2.getSequent)) sequents -= s2)
}
