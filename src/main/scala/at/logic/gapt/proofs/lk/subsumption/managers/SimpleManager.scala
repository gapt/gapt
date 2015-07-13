/*
 * SimpleManager.scala
 *
 */

package at.logic.gapt.proofs.lk.subsumption.managers

import at.logic.gapt.utils.patterns.listeners.ListenerManager
import at.logic.gapt.proofs.lk.subsumption._
import at.logic.gapt.proofs.lk.base.HOLSequent

class SimpleManager(
    listener: ListenerManager[SubsumptionDSEvent],
    sbsmpAlg: SubsumptionAlgorithm,
    iterator: () => Iterator[HOLSequent], // get the current iterator in every application
    exists:   ( HOLSequent => Boolean ) => Boolean,
    remove:   HOLSequent => Unit
) extends SubsumptionManager( listener, sbsmpAlg, iterator, exists, remove ) {
  init
  protected def addSequent( s: HOLSequent ) = ()
  protected def removeSequent( s: HOLSequent ) = ()

  def forwardSubsumption( s: HOLSequent ) = exists( ( s2: HOLSequent ) => sbsmpAlg.subsumes( s2, s ) )
  def backwardSubsumption( s: HOLSequent ) = iterator().foreach( s2 => if ( sbsmpAlg.subsumes( s, s2 ) ) remove( s2 ) )
}
