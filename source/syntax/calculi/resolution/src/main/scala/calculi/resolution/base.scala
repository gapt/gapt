/*
 * base.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.resolution

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol.propositions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap
import at.logic.language.hol.propositions.TypeSynonyms._


package base {

  private[resolution] object ResolutionFOFactory extends FOFactory {
    def createPrincipalFormulaOccurrence(formula: Formula, ancestors: List[FormulaOccurrence]) = createOccurrence(formula, ancestors)
    def createContextFormulaOccurrence(formula: Formula, ancestors: List[FormulaOccurrence]) = createOccurrence(formula, ancestors)
    def createOccurrence(formula: Formula, ancestors: List[FormulaOccurrence]) = new FormulaOccurrence(formula, ancestors) {def factory = ResolutionFOFactory}
  }

  case class Clause(negative: List[Formula], positive: List[Formula])
  case class ClauseOccurrence(negative: Seq[FormulaOccurrence], positive: Seq[FormulaOccurrence])

  trait ResolutionProof extends Proof[ClauseOccurrence]

  // method for creating the context of the lower sequent. Essentially creating nre occurrences
  // create new formula occurrences in the new context
  object createContext { def apply(set: Set[FormulaOccurrence]): Set[FormulaOccurrence] = set.map(x => x.factory.createContextFormulaOccurrence(x.formula, x::Nil)) }
}
