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

import at.logic.calculi.agraphProofs._
import collection.immutable.Seq

/*
  object RunningId {
    var id = 0
    def nextId = {id = id + 1; id}
  }
*/

  trait ResolutionProof[V <: Sequent] extends AGraphProof[V]

  trait NullaryResolutionProof[V <: Sequent] extends NullaryAGraphProof[V] with ResolutionProof[V] with NullaryProof[V]
  trait UnaryResolutionProof[V <: Sequent] extends UnaryAGraphProof[V] with ResolutionProof[V] with UnaryProof[V] {
    override def uProof = t.asInstanceOf[ResolutionProof[V]]
  }
  trait BinaryResolutionProof[V <: Sequent] extends BinaryAGraphProof[V] with ResolutionProof[V] with BinaryProof[V] {
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

trait CNF extends Sequent {require((antecedent++succedent).forall(x => x.formula match {case Atom(_,_) => true; case _ => false}))}

object IsNeg {
  def apply(formula: HOLFormula) = formula match {
    case Neg(_) => true
    case _ => false
  }
}
object StripNeg {
  def apply(formula: HOLFormula) = formula match {
    case Neg(f) => f
    case _ => formula
  }
}

/**
 * the sequences are actually multisets, as can be seen from the equal method
 */
trait FClause {
  def neg:Seq[Formula]
  def pos:Seq[Formula]
  def multisetEquals(f : FClause, g : FClause) : Boolean =
    f.neg.diff(g.neg).isEmpty && f.pos.diff(g.pos).isEmpty &&
      g.neg.diff(f.neg).isEmpty && g.pos.diff(f.pos).isEmpty

  override def equals(o: Any) = o match {
    case s: FClause => multisetEquals(this,s)
    case _ => false
  }
  override def hashCode = neg.size + pos.size
  override def toString = neg.foldLeft("")((s,x) => s + ", " + x.toString) + " |- "+ pos.foldLeft("")((s,x) => s + ", " + x.toString)
  /*
   compose constructs a sequent from two sequents. Corresponds to the 'o' operator in CERes
   should be moved to FSequent once FSequent is called Sequent (see Issue 201)
  */
  def compose(other: FClause) = new FClause{def neg = FClause.this.neg ++ other.neg; def pos =  FClause.this.pos ++ other.pos}
}

// a default factory
object FClause {
 def apply(n:Seq[Formula], p:Seq[Formula]): FClause = new FClause {def neg = n; def pos = p}
}

// the boolean represent isPositive as the negation is stripped from the literals
class Clause(val literals: Seq[Pair[FormulaOccurrence,Boolean]]) extends Sequent(
  literals.filter(!_._2).map(_._1),
  literals.filter(_._2).map(_._1)
) with CNF with FClause {
  def negative = antecedent
  def positive = succedent
  def neg = negative.map(_.formula)
  def pos = negative.map(_.formula)
}

object Clause {
  def apply(literals: Seq[Pair[FormulaOccurrence,Boolean]]) = new Clause(literals)
  def apply(neg: Seq[FormulaOccurrence], pos: Seq[FormulaOccurrence]) = new Clause(neg.map((_,false)) ++ pos.map((_,true)))
  def unapply(s: Sequent) = s match {
    case c: Clause => Some(c.negative, c.positive)
    case _ => None
  }
}

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
