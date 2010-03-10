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

  trait CNF extends Sequent {require((antecedent++succedent).forall(x => x match {case Atom(_,_) => true; case _ => false}))}
  class Clause(neg: List[HOLFormula], pos: List[HOLFormula]) extends Sequent(neg, pos) with CNF {
    def negative = antecedent.asInstanceOf[List[HOLFormula]]
    def positive = succedent.asInstanceOf[List[HOLFormula]]
    // set equivalence
    def formulaEquivalece(clause: Clause) =
      negative.size == clause.negative.size &&
      positive.size == clause.positive.size &&
      negative.forall(a => clause.negative.contains(a)) &&
      positive.forall(a => clause.positive.contains(a))
    def #=(clause: Clause) = formulaEquivalece(clause)
    // returns the n literal of the clause considering that the literals are ordered negative ++ positive
    def apply(n: Int) = if (n < negative.size) negative(n) else positive(n - negative.size)
    override def toString = 
      (if (negative.size > 1) negative.head.toString + negative.tail.foldLeft("")((s,a) => s+", "+a.toString)
      else negative.foldLeft("")((s,a) => s+a.toString)) + ":-" +
      (if (positive.size > 1) positive.head.toString + positive.tail.foldLeft("")((s,a) => s+", "+a.toString)
      else positive.foldLeft("")((s,a) => s+a.toString))
    def removeFormulasAtIndices(inds: List[Int]): Clause = Clause(
        negative.zipWithIndex.filter(x => !inds.contains(x._2)).map(x => x._1),
        positive.zipWithIndex.filter(x => !inds.contains(x._2)).map(x => x._1)
      )
  }
  object Clause {
    def apply(neg: List[HOLFormula], pos: List[HOLFormula]) = new Clause(neg,pos)
    def unapply(s: Sequent) = s match {
      case c: Clause => Some(c.negative, c.positive)
      case _ => None
    }
  }
  /*object Clause {
    def apply(negative: List[HOLFormula], positive: List[HOLFormula]) = new Clause(negative, positive)
    def unapply(a: Any) = a match {
      case c: Clause => Some(c.negative, c.positive)
      case _ => None
    }
  }*/

  trait ResolutionProof extends Proof[Clause] 
  trait UnaryResolutionProof extends UnaryTree[Clause] with ResolutionProof with UnaryProof[Clause] {
    override def uProof = t.asInstanceOf[ResolutionProof]
  }
  trait BinaryResolutionProof extends BinaryTree[Clause] with ResolutionProof with BinaryProof[Clause] {
    override def uProof1 = t1.asInstanceOf[ResolutionProof]
    override def uProof2 = t2.asInstanceOf[ResolutionProof]
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

  // to move to another file when its name is clear
  // 
  // axioms
  case object AxiomType extends NullaryRuleTypeA
  case object VariantType extends UnaryRuleTypeA
  case object FactorType extends UnaryRuleTypeA
  case object ResolutionType extends BinaryRuleTypeA

  object Axiom {
    def apply(cl: Clause): ResolutionProof = {
      new LeafTree[Clause](cl) with ResolutionProof {def rule = AxiomType}
    }
    def unapply(proof: ResolutionProof) = if (proof.rule == AxiomType) Some((proof.root)) else None
    // should be optimized as it was done now just to save coding time
  }

  // left side is always resolved on positive literal and right on negative
  object Resolution {
    def apply(p1: ResolutionProof, p2: ResolutionProof, i: Int, j: Int, sub: Substitution): ResolutionProof = {
      new BinaryTree[Clause](createClause(p1.root, p2.root, i, j, sub), p1, p2) with BinaryResolutionProof with LiteralIds with AppliedSubstitution
      {def rule = ResolutionType; def literalIdLeft = i; def literalIdRight = j; def substitution = sub}
    }
    // compose two clauses on all elements except with the index given and apply sub on all terms
    private def createClause(c1: Clause, c2: Clause, i: Int, j: Int, sub: Substitution) = {
      val (neg1,pos1) = if (i < c1.negative.size)
          (removeAtIndex(c1.negative, i), c1.positive)
        else (c1.negative, removeAtIndex(c1.positive, i - c1.negative.size))
      val (neg2,pos2) = if (j < c2.negative.size) 
          (removeAtIndex(c2.negative, j), c2.positive)
        else (c2.negative, removeAtIndex(c2.positive, j - c2.negative.size))
      Clause((neg1 ++ neg2).map(x => sub(x).asInstanceOf[HOLFormula]), (pos1 ++ pos2).map(x => sub(x).asInstanceOf[HOLFormula]))
    }
    private def removeAtIndex(ls: List[HOLFormula], i: Int) = ls.zipWithIndex.filter(x => x._2 != i).map(x => x._1)
    def unapply(proof: ResolutionProof) = if (proof.rule == ResolutionType) {
        val pr = proof.asInstanceOf[BinaryResolutionProof with LiteralIds with AppliedSubstitution]
        Some((pr.root, pr.uProof1, pr.uProof2, pr.literalIdLeft, pr.literalIdRight, pr.substitution))
      }
      else None
  }

  object Paramodulation {
    def apply(p1: ResolutionProof, p2: ResolutionProof, i: Int, j: Int, newLiteral: HOLFormula, sub: Substitution): ResolutionProof = {
      new BinaryTree[Clause](createClause(p1.root, p2.root, i, j, newLiteral, sub), p1, p2) with BinaryResolutionProof with LiteralIds with AppliedSubstitution
      {def rule = ResolutionType; def literalIdLeft = i; def literalIdRight = j; def substitution = sub}
    }
    // compose two clauses on all elements except with the index given and apply sub on all terms
    private def createClause(c1: Clause, c2: Clause, i: Int, j: Int, newLiteral: HOLFormula, sub: Substitution) = {
      val (neg1,pos1) = if (i < c1.negative.size)
          (removeAtIndex(c1.negative, i), c1.positive)
        else (c1.negative, removeAtIndex(c1.positive, i - c1.negative.size))
      val (neg2,pos2) = if (j < c2.negative.size)
          (newLiteral::removeAtIndex(c2.negative, j), c2.positive)
        else (c2.negative, newLiteral::removeAtIndex(c2.positive, j - c2.negative.size))
      Clause((neg1 ++ neg2).map(x => sub(x).asInstanceOf[HOLFormula]), (pos1 ++ pos2).map(x => sub(x).asInstanceOf[HOLFormula]))
    }
    private def removeAtIndex(ls: List[HOLFormula], i: Int) = ls.zipWithIndex.filter(x => x._2 != i).map(x => x._1)
    def unapply(proof: ResolutionProof) = if (proof.rule == ResolutionType) {
        val pr = proof.asInstanceOf[BinaryResolutionProof with LiteralIds with AppliedSubstitution]
        Some((pr.root, pr.uProof1, pr.uProof2, pr.literalIdLeft, pr.literalIdRight, pr.substitution))
      }
      else None
  }

  object Variant {
    def apply(p: ResolutionProof): ResolutionProof = {
      val varGen = new VariantGenerator(RunningId, "v")
      val newCl = Clause(
          p.root.negative.map(variantTerm(varGen)).asInstanceOf[List[HOLFormula]],
          p.root.positive.map(variantTerm(varGen)).asInstanceOf[List[HOLFormula]])
      // create a variant only if needed
      if (!(newCl #= p.root))
        new UnaryTree[Clause](newCl, p)
          with UnaryResolutionProof with AppliedSubstitution {def rule = VariantType; def substitution = Substitution(varGen.varsMap.elements)}
      else p
    }
    private def variantTerm(op: Var => Var)(t: HOLExpression): HOLExpression = t match {
      case v @ Var(VariableStringSymbol(_),_) if v.asInstanceOf[Var].isFree => op(v.asInstanceOf[Var]).asInstanceOf[HOLExpression]
      case v: Var => v
      case App(a,b) => App(variantTerm(op)(a.asInstanceOf[HOLExpression]), variantTerm(op)(b.asInstanceOf[HOLExpression])).asInstanceOf[HOLExpression]
      case Abs(x,a) => Abs(x, variantTerm(op)(a.asInstanceOf[HOLExpression])).asInstanceOf[HOLExpression]
    }
    def unapply(proof: ResolutionProof) = if (proof.rule == VariantType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof with AppliedSubstitution]
        Some((pr.root, pr.uProof, pr.substitution))
      }
      else None
  }

  object Factor {
    def apply(p: ResolutionProof, indicesToRemove: List[Int], sub: Substitution): ResolutionProof = {
      new UnaryTree[Clause](p.root.removeFormulasAtIndices(indicesToRemove), p)
        with UnaryResolutionProof with AppliedSubstitution {def rule = FactorType; def substitution = sub}
    }
    def unapply(proof: ResolutionProof) = if (proof.rule == FactorType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof with AppliedSubstitution]
        Some((pr.root, pr.uProof, pr.substitution))
      }
      else None
  }
}
