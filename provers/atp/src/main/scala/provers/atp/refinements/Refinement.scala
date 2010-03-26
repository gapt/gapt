/*
 * Refinement.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.refinements

import at.logic.calculi.resolution.base._
import at.logic.utils.patterns.listeners._
import at.logic.utils.ds.{Add, Remove, PublishingBuffer, PublishingBufferEvent}

trait Refinement {
  val clauses: PublishingBuffer[Clause]
  clauses.addListener((x: PublishingBufferEvent[Clause])=> x.ar match {
      case Remove => removeClause(x.elem)
      case Add => () // only refinements add clauses so they dont need to listen to that event
  })

  protected def removeClause(s: Clause): Unit

  def getNextClausesPair: Option[Tuple2[ResolutionProof, ResolutionProof]] // return the next pair
  def getClausesPair(c1: Clause, c2: Clause): Option[Tuple2[ResolutionProof, ResolutionProof]] // force the refinement to return a specific pair
  def insertProof(proof: ResolutionProof): Unit
}
