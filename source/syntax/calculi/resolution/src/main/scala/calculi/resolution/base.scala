 /*
 * base.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.resolution

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.acyclicGraphs._
import scala.collection.immutable.Set
import scala.collection.mutable.Map
import at.logic.language.lambda.substitutions._
import at.logic.calculi.lk.base._

package base {

/*
  object RunningId {
    var id = 0
    def nextId = {id = id + 1; id}
  }
*/

  trait ResolutionProof[V <: SequentOccurrence] extends Proof[V] with SequentLike {
    def getSequent = root.getSequent
  }
  trait NullaryResolutionProof[V <: SequentOccurrence] extends LeafAGraph[V] with ResolutionProof[V] with NullaryProof[V]
  trait UnaryResolutionProof[V <: SequentOccurrence] extends UnaryAGraph[V] with ResolutionProof[V] with UnaryProof[V] {
    override def uProof = t.asInstanceOf[ResolutionProof[V]]
  }
  trait BinaryResolutionProof[V <: SequentOccurrence] extends BinaryAGraph[V] with ResolutionProof[V] with BinaryProof[V] {
    override def uProof1 = t1.asInstanceOf[ResolutionProof[V]]
    override def uProof2 = t2.asInstanceOf[ResolutionProof[V]]
  }

/*
  trait LiteralId {
    def literalId: Int
  }

  trait LiteralIds {
    def literalIdLeft: Int
    def literalIdRight: Int
  }

  trait LiteralIdsSets {
    def literalIdsLeft: List[Int]
    def literalIdsRight: List[Int]
  }
*/

  trait InstantiatedVariable {
    def term: HOLExpression
  }
  trait AppliedSubstitution[T <: LambdaExpression] {
    def substitution: Substitution[T]
  }
  // method for creating the context of the lower sequent. Essentially creating nre occurrences
  // create new formula occurrences in the new context
  //object createContext { def apply(set: Set[FormulaOccurrence]): Set[FormulaOccurrence] = set.map(x => x.factory.createContextFormulaOccurrence(x.formula, x, x::Nil, Set[FormulaOccurrence]())) }

  case object InitialType extends NullaryRuleTypeA

  object InitialSequent {
    def apply[V <: SequentOccurrence](seq: Sequent)(implicit factory: FOFactory) = {
      val left: Set[FormulaOccurrence] = seq.antecedent.foldLeft(Set.empty[FormulaOccurrence])((st, form) => st + createOccurrence(form, st, factory))
      val right: Set[FormulaOccurrence] = seq.succedent.foldLeft(Set.empty[FormulaOccurrence])((st, form) => st + createOccurrence(form, st, factory))
      new LeafAGraph[SequentOccurrence](SequentOccurrence(left, right)) with NullaryResolutionProof[V] {def rule = InitialType}
    }

    def createOccurrence(f: HOLFormula, others: Set[FormulaOccurrence], factory: FOFactory): FormulaOccurrence = factory.createPrincipalFormulaOccurrence(f, Nil, others)

    def unapply[V <: SequentOccurrence](proof: ResolutionProof[V]) = if (proof.rule == InitialType) Some((proof.root)) else None
    // should be optimized as it was done now just to save coding time
  }

  // exceptions
  class ResolutionRuleException(msg: String) extends RuleException(msg)
  class ResolutionRuleCreationException(msg: String) extends ResolutionRuleException(msg)
}
