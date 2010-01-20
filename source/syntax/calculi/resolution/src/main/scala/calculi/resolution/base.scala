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
  case class ClauseOccurrence(negative: Set[FormulaOccurrence], positive: Set[FormulaOccurrence]) {
    def formulaEquivalece(clause: Clause) = negative.size == clause.negative.size &&
                                            positive.size == clause.positive.size &&
                                            negative.forall(a => clause.negative.contains(a.formula)) &&
                                            positive.forall(a => clause.positive.contains(a.formula))
  }

  trait ResolutionProof extends Proof[ClauseOccurrence]

  // method for creating the context of the lower sequent. Essentially creating nre occurrences
  // create new formula occurrences in the new context
  object createContext { def apply(set: Set[FormulaOccurrence]): Set[FormulaOccurrence] = set.map(x => x.factory.createContextFormulaOccurrence(x.formula, x::Nil)) }

  // to move to another file when its name is clear
  // 
  // axioms
  case object InitialRuleType extends NullaryRuleTypeA

  object Axiom {
    def apply(cl: Clause): ResolutionProof = {
      val neg: List[FormulaOccurrence] = cl.negative.map(createOccurrence)
      val pos: List[FormulaOccurrence] = cl.positive.map(createOccurrence)
      new LeafTree[ClauseOccurrence](ClauseOccurrence(toSet(neg), toSet(pos))) with ResolutionProof {def rule = InitialRuleType}
    }
    def createOccurrence(f: Formula): FormulaOccurrence = ResolutionFOFactory.createOccurrence(f, Nil)
    def unapply(proof: ResolutionProof) = if (proof.rule == InitialRuleType) Some((proof.root)) else None
    // should be optimized as it was done now just to save coding time
    def toSet[T](list: List[T]) = {
      def traverse(list: List[T])(set: Set[T]): Set[T] = list match {
        case hd :: tail => traverse(tail)(set + hd)   // create a new Set, adding hd
        case Nil => set
      }
      traverse(list)(Set[T]())
    }
  }
}
