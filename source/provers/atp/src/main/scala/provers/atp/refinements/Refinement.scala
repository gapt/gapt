/*
 * Refinement.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.refinements

import at.logic.calculi.resolution.base._
import at.logic.calculi.lk.base._
import at.logic.utils.patterns.listeners._
import at.logic.utils.ds.{Add, Remove, PublishingBuffer, PublishingBufferEvent}

trait Refinement[V <: Sequent] {
  val clauses: PublishingBuffer[V]
  
  protected def init =  clauses.addListener((x: PublishingBufferEvent[V])=> x.ar match {
      case Remove => removeClause(x.elem)
      case Add => () // only refinements add clauses so they dont need to listen to that event
  })
  
  protected def removeClause(s: V): Unit

  def getNextClausesPair: Option[Tuple2[ResolutionProof[V], ResolutionProof[V]]] // return the next pair
  def getClausesPair(c1: V, c2: V): Option[Tuple2[ResolutionProof[V], ResolutionProof[V]]] // force the refinement to return a specific pair
  def insertProof(proof: ResolutionProof[V]): Unit
}
