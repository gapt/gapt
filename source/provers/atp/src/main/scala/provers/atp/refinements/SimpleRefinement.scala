/*
 * SimpleRefinement.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.refinements

import scala.collection.mutable.Queue
import at.logic.calculi.resolution.base._

trait SimpleRefinement extends Refinement {
  val queue = new Queue[Tuple2[ResolutionProof,ResolutionProof]]
  val clauses = new Queue[ResolutionProof]
  
  def getClauses: Option[Tuple2[ResolutionProof, ResolutionProof]] = try {
    Some(queue.dequeue)
  } catch {
    case ex: Predef.NoSuchElementException => None
  }
  def insertClauses(c: List[Clause]) = {
    clauses ++= c.map(createInitialProof)
    clauses.foreach(addPairs) // should remove for the argument all previous clauses for optimization as otherwise we have lots of duplicates
  }
  def insertProof(proof: ResolutionProof) = {addPairs(proof); clauses.enqueue(proof)}

  private def createInitialProof(c: Clause): ResolutionProof = Axiom(c)
  private def addPairs(proof: ResolutionProof) = clauses.foreach(x =>
    if (x != proof) queue += (proof,x)
  )
}
