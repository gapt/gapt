/*
 * SubsumptionManager.scala
 *
 * Managers are used to manage a buffer of sequents that a subsumption is tested against.
 * The buffer notifies the manager when elements are added or removed so it can update its
 * internal datastructures.
 */

package at.logic.gapt.proofs.lk.subsumption.managers

import at.logic.gapt.utils.patterns.listeners._
import at.logic.gapt.proofs.lk.subsumption._
import at.logic.gapt.proofs.lk.base.HOLSequent

// this is used in order to make the manager listen for changes on data structures using the manager, so it will be updated accordingly
case class SubsumptionDSEvent( ar: SAddRemove, elem: HOLSequent )
sealed abstract class SAddRemove
case object SAdd extends SAddRemove
case object SRemove extends SAddRemove

abstract class SubsumptionManager(
    val listener: ListenerManager[SubsumptionDSEvent],
    val sbsmpAlg: SubsumptionAlgorithm,
    val iterator: () => Iterator[HOLSequent],
    val exists:   ( HOLSequent => Boolean ) => Boolean,
    val remove:   HOLSequent => Unit
) {
  protected def init = listener.addListener( ( x: SubsumptionDSEvent ) => x.ar match {
    case SAdd    => addSequent( x.elem )
    case SRemove => removeSequent( x.elem )
  } )

  // checks if s is being subsumed by any of the sequents managed by the manager
  def forwardSubsumption( s: HOLSequent ): Boolean
  // removes any sequent that is subsumed by s
  def backwardSubsumption( s: HOLSequent ): Unit

  protected def addSequent( s: HOLSequent ): Unit
  protected def removeSequent( s: HOLSequent ): Unit
}
