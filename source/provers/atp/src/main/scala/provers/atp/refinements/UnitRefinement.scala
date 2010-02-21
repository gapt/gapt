/*
 * UnitRefinement.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.refinements

import at.logic.calculi.resolution.base._
import scala.collection.mutable.{Queue,ListBuffer}
import at.logic.utils.ds.PublishingBuffer

class UnitRefinement(c: PublishingBuffer[Clause]) extends Refinement {
  val clauses = c // all clauses
  val pairs = new ListBuffer[Tuple2[ResolutionProof,ResolutionProof]] // all pairs of possible two clauses
  val proofs = new ListBuffer[ResolutionProof] // all clauses as proofs
  val units: ListBuffer[ResolutionProof] = new ListBuffer[ResolutionProof]()
  insertClauses

  def getNextClausesPair: Option[Tuple2[ResolutionProof, ResolutionProof]] = if (pairs.isEmpty) None else Some(pairs.remove(0))

  private def insertClauses = {
    proofs ++= clauses.map(createInitialProof)
    units ++= proofs.filter(x => isUnit(x.root))
    val tmp = proofs.toList
    pairs ++= (for (
        c1 <- units;
        c2 <- proofs;
        if (!(c1.root.antecedent.isEmpty && c2.root.antecedent.isEmpty) &&
          !(c1.root.succedent.isEmpty && c2.root.succedent.isEmpty) &&
          c1.root != c2.root)
      ) yield (c1,c2))
  }
  def insertProof(proof: ResolutionProof) = {
    clauses.append(proof.root)
    pairs ++= {for (
        c1 <- (if (isUnit(proof.root)) proofs else units);
        if (!(c1.root.antecedent.isEmpty && proof.root.antecedent.isEmpty) &&
          !(c1.root.succedent.isEmpty && proof.root.succedent.isEmpty))
      ) yield (c1,proof)
    }
    proofs += proof
    if (isUnit(proof.root)) units += proof
  }

  protected def removeClause(s: Clause) = {
    proofs.filter(x => x.root == s).foreach(x => proofs -= x)
    pairs.filter(x => x._1.root == s || x._2.root == s).foreach(x => pairs -= x)
  }
  private def createInitialProof(c: Clause): ResolutionProof = Axiom(c)
  private def isUnit(c: Clause): Boolean = (c.negative.size + c.positive.size) == 1
}

  /*
trait UnitRefinement  extends Refinement {
  val queue: Queue[Tuple2[ResolutionProof,ResolutionProof]] = new Queue[Tuple2[ResolutionProof,ResolutionProof]]()
  val clauses:ListBuffer[ResolutionProof] = new ListBuffer[ResolutionProof]()
  val units: ListBuffer[ResolutionProof] = new ListBuffer[ResolutionProof]()
  
  def getClauses = try {
      Some(queue.dequeue)
    } catch {
      case ex: Predef.NoSuchElementException => None
  }
  def insertClauses(c: List[Clause]) = {
    clauses ++= c.map(x => Axiom(x))
    units ++= clauses.filter(x => isUnit(x.root))
    queue ++= {for (
        c1 <- units;
        c2 <- clauses;
        if (!(c1.root.antecedent.isEmpty && c2.root.antecedent.isEmpty) &&
          !(c1.root.succedent.isEmpty && c2.root.succedent.isEmpty) &&
          c1.root != c2.root)
      ) yield (c1,c2)
    }
  }
  def insertProof(proof: ResolutionProof) = {
    queue ++= {for (
        c1 <- units;
        if (!(c1.root.antecedent.isEmpty && proof.root.antecedent.isEmpty) &&
          !(c1.root.succedent.isEmpty && proof.root.succedent.isEmpty))
      ) yield (c1,proof)
    }
    clauses += proof
    if (isUnit(proof.root)) units += proof
  }
  private def isUnit(c: Clause): Boolean = (c.negative.size + c.positive.size) == 1
}
*/