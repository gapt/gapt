/*
 * Refinement.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.refinements

import at.logic.calculi.resolution.base._

trait Refinement {
  def getClauses: Option[Tuple2[ResolutionProof, ResolutionProof]]
  def insertClauses(clauses: List[Clause]): Unit
  def insertProof(proof: ResolutionProof): Unit
}
