/*
 * SubsumptionManager.scala
 *
 * Managers are used to manage a buffer of sequents that a subsumption is tested against.
 * The buffer notifies the manager when elements are added or removed so it can update its
 * internal datastructures.
 */

package at.logic.algorithms.subsumption.managers

import at.logic.utils.patterns.listeners._
import at.logic.algorithms.subsumption._
import at.logic.calculi.lk.base.FSequent

// this is used in order to make the manager listen for changes on data structures using the manager, so it will be updated accordingly
case class SubsumptionDSEvent(ar: SAddRemove, elem: FSequent)
sealed abstract class SAddRemove
case object SAdd extends SAddRemove
case object SRemove extends SAddRemove

abstract class SubsumptionManager(val listener: ListenerManager[SubsumptionDSEvent],
                                  val sbsmpAlg: SubsumptionAlgorithm,
                                  val iterator: () => Iterator[FSequent],
                                  val exists: (FSequent => Boolean) => Boolean,
                                  val remove: FSequent => Unit) {
  protected def init = listener.addListener((x: SubsumptionDSEvent)=> x.ar match {
      case SAdd => addSequent(x.elem)
      case SRemove => removeSequent(x.elem)
  })

  // checks if s is being subsumed by any of the sequents managed by the manager
  def forwardSubsumption(s: FSequent): Boolean
  // removes any sequent that is subsumed by s
  def backwardSubsumption(s: FSequent): Unit

  protected def addSequent(s: FSequent): Unit
  protected def removeSequent(s: FSequent): Unit
}
