/*
 * SimpleRefinement.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.refinements

import scala.collection.mutable.{Queue,ListBuffer}
import at.logic.calculi.resolution.base._

trait SimpleRefinement extends Refinement {
  var queue: Queue[Tuple2[ResolutionProof,ResolutionProof]] = null
  var clauses:ListBuffer[ResolutionProof] = null
  
  def getClauses: Option[Tuple2[ResolutionProof, ResolutionProof]] = try {
    Some(queue.dequeue)
  } catch {
    case ex: Predef.NoSuchElementException => None
  }
  def insertClauses(c: List[Clause]) = {
    clauses = new ListBuffer[ResolutionProof]
    queue = new Queue[Tuple2[ResolutionProof,ResolutionProof]]
    clauses ++= c.map(createInitialProof)
    val tmp = clauses.toList
    queue ++= (for {
      (a,i) <- tmp.zip(tmp.indices)
      j <- tmp.indices
      if (j > i)
    } yield (a, clauses(j)))
  }
  def insertProof(proof: ResolutionProof) = {queue ++= clauses.map(a => (proof, a)); clauses += proof}
  private def createInitialProof(c: Clause): ResolutionProof = Axiom(c)
}
