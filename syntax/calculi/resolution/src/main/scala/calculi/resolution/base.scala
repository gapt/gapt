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
import at.logic.utils.traits.Occurrence

package base {

import collection.immutable.Seq

/*
  object RunningId {
    var id = 0
    def nextId = {id = id + 1; id}
  }
*/

  trait ResolutionProof[V <: Sequent] extends Proof[V]
  trait NullaryResolutionProof[V <: Sequent] extends LeafAGraph[V] with ResolutionProof[V] with NullaryProof[V]
  trait UnaryResolutionProof[V <: Sequent] extends UnaryAGraph[V] with ResolutionProof[V] with UnaryProof[V] {
    override def uProof = t.asInstanceOf[ResolutionProof[V]]
  }
  trait BinaryResolutionProof[V <: Sequent] extends BinaryAGraph[V] with ResolutionProof[V] with BinaryProof[V] {
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

  case object InitialType extends NullaryRuleTypeA

  object InitialSequent {
    def apply[V <: Sequent](ant: Seq[HOLFormula], suc: Seq[HOLFormula]) (implicit factory: FOFactory) = {
      val left: Seq[FormulaOccurrence] = ant.map(factory.createFormulaOccurrence(_,Nil))
      val right: Seq[FormulaOccurrence] = suc.map(factory.createFormulaOccurrence(_,Nil))
      new LeafAGraph[Sequent](Sequent(left, right)) with NullaryResolutionProof[V] {def rule = InitialType}
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == InitialType) Some((proof.root)) else None
    // should be optimized as it was done now just to save coding time
  }

  // exceptions
  class ResolutionRuleException(msg: String) extends RuleException(msg)
  class ResolutionRuleCreationException(msg: String) extends ResolutionRuleException(msg)
}
