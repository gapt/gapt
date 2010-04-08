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
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.Map
import at.logic.language.lambda.substitutions._
import at.logic.calculi.lk.base._

package base {

  object RunningId {
    var id = 0
    def nextId = {id = id + 1; id}
  }

  trait ResolutionProof[V <: Sequent] extends Proof[V]
  trait UnaryResolutionProof[V <: Sequent] extends UnaryTree[V] with ResolutionProof[V] with UnaryProof[V] {
    override def uProof = t.asInstanceOf[ResolutionProof[V]]
  }
  trait BinaryResolutionProof[V <: Sequent] extends BinaryTree[V] with ResolutionProof[V] with BinaryProof[V] {
    override def uProof1 = t1.asInstanceOf[ResolutionProof[V]]
    override def uProof2 = t2.asInstanceOf[ResolutionProof[V]]
  }

  trait LiteralIds {
    def literalIdLeft: Int
    def literalIdRight: Int
  }

  trait AppliedSubstitution {
    def substitution: Substitution
  }
  // method for creating the context of the lower sequent. Essentially creating nre occurrences
  // create new formula occurrences in the new context
  object createContext { def apply(set: Set[FormulaOccurrence]): Set[FormulaOccurrence] = set.map(x => x.factory.createContextFormulaOccurrence(x.formula, x::Nil)) }

  case object InitiaType extends NullaryRuleTypeA

  object InitialSequent {
    def apply[V <: Sequent](cl: V): ResolutionProof[V] = {
      new LeafTree[V](cl) with ResolutionProof[V] {def rule = InitiaType}
    }
    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == InitiaType) Some((proof.root)) else None
    // should be optimized as it was done now just to save coding time
  }
}
