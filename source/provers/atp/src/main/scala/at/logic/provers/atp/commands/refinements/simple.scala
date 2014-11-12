
package at.logic.provers.atp.commands.refinements.simple

import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.resolution.ResolutionProof
import at.logic.provers.atp.commands.base.InitialCommand
import at.logic.provers.atp.commands.refinements.base.{Refinement,RefinementID}
import at.logic.provers.atp.Definitions._
import at.logic.utils.ds.PublishingBuffer
import collection.mutable.ListBuffer

// the command
case class SimpleRefinementGetCommand[V <: Sequent]() extends InitialCommand[V] {
  def apply(state: State) = {
    val refinement =
      if (state.isDefinedAt(RefinementID())) state(RefinementID()).asInstanceOf[SimpleRefinement[V]]
      else {
        val ref = new SimpleRefinement(state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]])
        state += new Tuple2(RefinementID(), ref)
        ref
      }
    refinement.getNext match {
      case None => List()
      case Some(p) => List((state, p))
    }
  }

  override def toString = "SimpleRefinementGetCommand()"

}

private[refinements] class SimpleRefinement[V <: Sequent](clauses: PublishingBuffer[ResolutionProof[V]]) extends Refinement[V](clauses) {
  val pairs = new ListBuffer[Tuple2[ResolutionProof[V],ResolutionProof[V]]] // all pairs of possible two clauses
  insertClauses
  def getNext: Option[Tuple2[ResolutionProof[V],ResolutionProof[V]]] = if (isEmpty) None else Some(pairs.remove(0))

  private def insertClauses = {
    val tmp = clauses.toList
    pairs ++= (for {
      (a,i) <- tmp.zip(tmp.indices)
      j <- tmp.indices
      if (j > i)
    } yield (a, clauses(j)))
  }
  protected def addClause(s: ResolutionProof[V]) = {
    pairs ++= clauses.map(a => (s, a))
  }
  protected def removeClause(s: ResolutionProof[V]) = {
    pairs.filter(x => (x._1.root syntacticMultisetEquals s.root) || (x._2.root syntacticMultisetEquals s.root)).foreach(x => pairs -= x)
  }
  def isEmpty: Boolean = pairs.isEmpty

  override def toString = "SimpleRefinement("+clauses+")"

}

