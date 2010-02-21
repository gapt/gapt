/*
 * SimpleRefinement.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.refinements

import scala.collection.mutable.{Queue,ListBuffer}
import at.logic.calculi.resolution.base._
import at.logic.utils.ds.PublishingBuffer

class SimpleRefinement(c: PublishingBuffer[Clause]) extends Refinement {
  val clauses = c // all clauses
  val pairs = new ListBuffer[Tuple2[ResolutionProof,ResolutionProof]] // all pairs of possible two clauses
  val proofs = new ListBuffer[ResolutionProof] // all clauses as proofs
  insertClauses
  
  def getNextClausesPair: Option[Tuple2[ResolutionProof, ResolutionProof]] = if (pairs.isEmpty) None else Some(pairs.remove(0))

  private def insertClauses = {
    proofs ++= clauses.map(createInitialProof)
    val tmp = proofs.toList
    pairs ++= (for {
      (a,i) <- tmp.zip(tmp.indices)
      j <- tmp.indices
      if (j > i)
    } yield (a, proofs(j)))
  }
  def insertProof(proof: ResolutionProof) = {
    clauses.append(proof.root)
    proofs += proof
    pairs ++= proofs.map(a => (proof, a))
  }

  protected def removeClause(s: Clause) = {
    proofs.filter(x => x.root == s).foreach(x => proofs -= x)
    pairs.filter(x => x._1.root == s || x._2.root == s).foreach(x => pairs -= x)
  }
  private def createInitialProof(c: Clause): ResolutionProof = Axiom(c)
}
