/*
 * SimpleRefinement.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.refinements

import scala.collection.mutable.{Queue,ListBuffer}
import at.logic.calculi.resolution.base._
import at.logic.calculi.lk.base._
import at.logic.utils.ds.PublishingBuffer

class SimpleRefinement[V <: Sequent](c: PublishingBuffer[V]) extends Refinement[V] {
  val clauses = c // all clauses
  val pairs = new ListBuffer[Tuple2[ResolutionProof[V],ResolutionProof[V]]] // all pairs of possible two clauses
  val proofs = new ListBuffer[ResolutionProof[V]] // all clauses as proofs
  insertClauses
  
  def getNextClausesPair: Option[Tuple2[ResolutionProof[V], ResolutionProof[V]]] = if (pairs.isEmpty) None else Some(pairs.remove(0))

  def getClausesPair(c1: V, c2: V): Option[Tuple2[ResolutionProof[V], ResolutionProof[V]]] = {
    val pairInd = pairs.findIndexOf(x => (x._1.root == c1 && x._2.root == c2) || (x._1.root == c2 && x._2.root == c1))
    if (pairInd > -1) {val ret = pairs(pairInd); pairs.remove(pairInd); Some(ret)}
    else None
  }

  private def insertClauses = {
    proofs ++= clauses.map(createInitialProof)
    val tmp = proofs.toList
    pairs ++= (for {
      (a,i) <- tmp.zip(tmp.indices)
      j <- tmp.indices
      if (j > i)
    } yield (a, proofs(j)))
  }
  def insertProof(proof: ResolutionProof[V]) = {
    clauses.append(proof.root)
    proofs += proof
    pairs ++= proofs.map(a => (proof, a))
  }

  protected def removeClause(s: V) = {
    proofs.filter(x => x.root == s).foreach(x => proofs -= x)
    pairs.filter(x => x._1.root == s || x._2.root == s).foreach(x => pairs -= x)
  }
  private def createInitialProof(c: V): ResolutionProof[V] = InitialSequent(c)
}
