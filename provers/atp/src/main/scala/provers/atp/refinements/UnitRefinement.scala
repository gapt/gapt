/*
 * UnitRefinement.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.refinements

import at.logic.calculi.resolution.base._
import scala.collection.mutable.{Queue,ListBuffer}

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
    units ++= clauses.filter(x => x.root.antecedent.isEmpty || x.root.succedent.isEmpty)
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
    if (proof.root.antecedent.isEmpty || proof.root.succedent.isEmpty) units += proof
  }
}
