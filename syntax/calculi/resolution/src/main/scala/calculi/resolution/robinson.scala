/*
 * robinson.scala
 *
 * Traditional resolution calculus with factors and para modulation. Using clauses
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
import base._

package robinson {

  trait CNF extends Sequent {require((antecedent++succedent).forall(x => x match {case Atom(_,_) => true; case _ => false}))}
  class Clause(neg: List[HOLFormula], pos: List[HOLFormula]) extends Sequent(neg, pos) with CNF {
    def negative = antecedent.asInstanceOf[List[HOLFormula]]
    def positive = succedent.asInstanceOf[List[HOLFormula]]
    override def removeFormulasAtIndices(inds: List[Int]): Clause = Clause(
        negative.zipWithIndex.filter(x => !inds.contains(x._2)).map(x => x._1),
        positive.zipWithIndex.filter(x => !inds.contains(x._2 + negative.size)).map(x => x._1)
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

  case object VariantType extends UnaryRuleTypeA
  case object FactorType extends UnaryRuleTypeA
  case object ResolutionType extends BinaryRuleTypeA

  // left side is always resolved on positive literal and right on negative
  object Resolution {
    def apply[T <: HOLExpression](p1: ResolutionProof[Clause], p2: ResolutionProof[Clause], i: Int, j: Int, sub: Substitution[T]): ResolutionProof[Clause] = {
      new BinaryAGraph[Clause](createClause(p1.root.asInstanceOf[Clause], p2.root.asInstanceOf[Clause], i, j, sub), p1, p2) with BinaryResolutionProof[Clause] with LiteralIds with AppliedSubstitution[T]
      {def rule = ResolutionType; def literalIdLeft = i; def literalIdRight = j; def substitution = sub}
    }
    // compose two clauses on all elements except with the index given and apply sub on all terms
    private def createClause[T <: LambdaExpression](c1: Clause, c2: Clause, i: Int, j: Int, sub: Substitution[T]) = {
      val (neg1,pos1) = if (i < c1.negative.size)
          (removeAtIndex(c1.negative, i), c1.positive)
        else (c1.negative, removeAtIndex(c1.positive, i - c1.negative.size))
      val (neg2,pos2) = if (j < c2.negative.size)
          (removeAtIndex(c2.negative, j), c2.positive)
        else (c2.negative, removeAtIndex(c2.positive, j - c2.negative.size))
      Clause((neg1 ++ neg2).map(x => sub(x.asInstanceOf[T]).asInstanceOf[HOLFormula]), (pos1 ++ pos2).map(x => sub(x.asInstanceOf[T]).asInstanceOf[HOLFormula]))
    }
    private def removeAtIndex(ls: List[HOLFormula], i: Int) = ls.zipWithIndex.filter(x => x._2 != i).map(x => x._1)
    def unapply[T <: HOLExpression](proof: ResolutionProof[Clause]) = if (proof.rule == ResolutionType) {
        val pr = proof.asInstanceOf[BinaryResolutionProof[Clause] with LiteralIds with AppliedSubstitution[T]]
        Some((pr.root, pr.uProof1, pr.uProof2, pr.literalIdLeft, pr.literalIdRight, pr.substitution))
      }
      else None
  }

  object Paramodulation {
    def apply[T <: HOLExpression](p1: ResolutionProof[Clause], p2: ResolutionProof[Clause], i: Int, j: Int, newLiteral: HOLFormula, sub: Substitution[T]): ResolutionProof[Clause] = {
      new BinaryAGraph[Clause](createClause(p1.root, p2.root, i, j, newLiteral, sub), p1, p2) with BinaryResolutionProof[Clause] with LiteralIds with AppliedSubstitution[T]
      {def rule = ResolutionType; def literalIdLeft = i; def literalIdRight = j; def substitution = sub}
    }
    // compose two clauses on all elements except with the index given and apply sub on all terms
    private def createClause[T <: HOLExpression](c1: Clause, c2: Clause, i: Int, j: Int, newLiteral: HOLFormula, sub: Substitution[T]) = {
      val (neg1,pos1) = if (i < c1.negative.size)
          (removeAtIndex(c1.negative, i), c1.positive)
        else (c1.negative, removeAtIndex(c1.positive, i - c1.negative.size))
      val (neg2,pos2) = if (j < c2.negative.size)
          (newLiteral::removeAtIndex(c2.negative, j), c2.positive)
        else (c2.negative, newLiteral::removeAtIndex(c2.positive, j - c2.negative.size))
      Clause((neg1 ++ neg2).map(x => sub(x.asInstanceOf[T]).asInstanceOf[HOLFormula]), (pos1 ++ pos2).map(x => sub(x.asInstanceOf[T]).asInstanceOf[HOLFormula]))
    }
    private def removeAtIndex(ls: List[HOLFormula], i: Int) = ls.zipWithIndex.filter(x => x._2 != i).map(x => x._1)
    def unapply[T <: HOLExpression](proof: ResolutionProof[Clause]) = if (proof.rule == ResolutionType) {
        val pr = proof.asInstanceOf[BinaryResolutionProof[Clause] with LiteralIds with AppliedSubstitution[T]]
        Some((pr.root, pr.uProof1, pr.uProof2, pr.literalIdLeft, pr.literalIdRight, pr.substitution))
      }
      else None
  }

  object Variant {
    def apply(p: ResolutionProof[Clause]): ResolutionProof[Clause] = {
      val varGen = new VariantGenerator(RunningId, "v")
      val newCl = Clause(
          p.root.negative.map(variantTerm(varGen)).asInstanceOf[List[HOLFormula]],
          p.root.positive.map(variantTerm(varGen)).asInstanceOf[List[HOLFormula]])
      // create a variant only if needed
      if (newCl != p.root)
        new UnaryAGraph[Clause](newCl, p)
          with UnaryResolutionProof[Clause] with AppliedSubstitution[HOLExpression] {def rule = VariantType; def substitution = Substitution(varGen.varsMap.elements.asInstanceOf[Iterator[Tuple2[Var,HOLExpression]]])}
      else p
    }
    private def variantTerm(op: Var => Var)(t: HOLExpression): HOLExpression = t match {
      case v @ Var(VariableStringSymbol(_),_) if v.asInstanceOf[Var].isFree => op(v.asInstanceOf[Var]).asInstanceOf[HOLExpression]
      case v: Var => v
      case App(a,b) => App(variantTerm(op)(a.asInstanceOf[HOLExpression]), variantTerm(op)(b.asInstanceOf[HOLExpression])).asInstanceOf[HOLExpression]
      case Abs(x,a) => Abs(x, variantTerm(op)(a.asInstanceOf[HOLExpression])).asInstanceOf[HOLExpression]
    }
    def unapply[T <: HOLExpression](proof: ResolutionProof[Clause]) = if (proof.rule == VariantType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[Clause] with AppliedSubstitution[T]]
        Some((pr.root, pr.uProof, pr.substitution))
      }
      else None
  }

  // the substitution contains also the substitutions generated by the resolution step happening later. We apply it now as it does not contain temporary substitutions for example:
  // we first resolve p(y), p(x), -p(f(y) with -p(a) to get p(y), -p(f(y)) with x -> a and then we look for possible factors, like y -> x and get the factor p(x), -p(f(x))
  // with substitution y -> x and x -> a. but as we combine the substitutions we cannot remove the substitution generated by the first step. This is not important as we apply
  // the same resolution step and therefore this substitution should be anyway generated.
  object Factor {
    def apply[T <: HOLExpression](p: ResolutionProof[Clause], indicesToRemove: List[Int], sub: Substitution[T]): ResolutionProof[Clause] = {
      new UnaryAGraph[Clause]({val r = p.root.removeFormulasAtIndices(indicesToRemove); Clause(r.negative.map(x => sub(x.asInstanceOf[T]).asInstanceOf[HOLFormula]), r.positive.map(x => sub(x.asInstanceOf[T]).asInstanceOf[HOLFormula]))}, p)
        with UnaryResolutionProof[Clause] with AppliedSubstitution[T] {def rule = FactorType; def substitution = sub}
    }
    def unapply[T <: HOLExpression](proof: ResolutionProof[Clause]) = if (proof.rule == FactorType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[Clause] with AppliedSubstitution[T]]
        Some((pr.root, pr.uProof, pr.substitution))
      }
      else None
  }
}
