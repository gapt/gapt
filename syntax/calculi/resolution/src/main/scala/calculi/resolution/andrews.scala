/*
 * andrews.scala
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
import base._
import at.logic.utils.labeling._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._

package andrews {
  case class LabeledSequent(antecedentLabeled: List[Tuple2[HOLFormula,Labeled[List[HOLExpression]]]], succedentLabeled: List[Tuple2[HOLFormula,Labeled[List[HOLExpression]]]])
      extends Sequent(antecedentLabeled.map(_._1), succedentLabeled.map(_._1)) {
    override def removeFormulasAtIndices(inds: List[Int]) = LabeledSequent(
        antecedentLabeled.zipWithIndex.filter(x => !inds.contains(x._2)).map(x => x._1),
        succedentLabeled.zipWithIndex.filter(x => !inds.contains(x._2 + antecedentLabeled.size)).map(x => x._1)
      )
    // the following methods return both the antecedent/succedent without the formula and the removed formula
    def getAntecedentPairAtIndex(index: Int) = (antecedentLabeled(index), antecedentLabeled.zipWithIndex.remove(x => x._2 == index).map(x => x._1))
    def getSuccedentPairAtIndex(index: Int) = (succedentLabeled(index), succedentLabeled.zipWithIndex.remove(x => x._2 == index).map(x => x._1))
  }

  case object NotTType extends UnaryRuleTypeA
  case object NotFType extends UnaryRuleTypeA
  case object OrTType extends UnaryRuleTypeA
  case object OrFLType extends UnaryRuleTypeA
  case object OrFRType extends UnaryRuleTypeA
  case object AllTType extends UnaryRuleTypeA
  case object AllFType extends UnaryRuleTypeA
  case object SubType extends UnaryRuleTypeA
  case object CutType extends BinaryRuleTypeA

  // all indices are locally to the side (so both on right and left sides it starts from 0

  object Cut {
    def apply(p1: ResolutionProof[LabeledSequent], p2: ResolutionProof[LabeledSequent], leftIndices: List[Int], rightIndices: List[Int]): ResolutionProof[LabeledSequent] = {
      new BinaryAGraph[LabeledSequent](createClause(p1.root.asInstanceOf[LabeledSequent], p2.root.asInstanceOf[LabeledSequent], leftIndices, rightIndices), p1, p2) with BinaryResolutionProof[LabeledSequent] with LiteralIdsSets
      {def rule = CutType; def literalIdsLeft = leftIndices; def literalIdsRight = rightIndices}
    }
    // compose two clauses on all elements except with the index given and apply sub on all terms
    private def createClause(c1: LabeledSequent, c2: LabeledSequent, leftIndices: List[Int], rightIndices: List[Int]) = {
      val c1m = c1.removeFormulasAtIndices(leftIndices.map(_+c1.antecedentLabeled.size))
      val c2m = c2.removeFormulasAtIndices(rightIndices)
      LabeledSequent(c1m.antecedentLabeled ++ c2m.antecedentLabeled, c1m.succedentLabeled ++ c2m.succedentLabeled)
    }
  }

  object NotT {
    def apply(p: ResolutionProof[LabeledSequent], index: Int): ResolutionProof[LabeledSequent] = {
      val pair = p.root.getSuccedentPairAtIndex(index)
      pair._1._1 match {
        case Neg(f) => new UnaryAGraph[LabeledSequent](LabeledSequent((f,pair._1._2) :: p.root.antecedentLabeled, pair._2), p)
          with UnaryResolutionProof[LabeledSequent] with LiteralId {def rule = NotTType; def literalId = index}
        case _ => throw new RuleException("Andrews resolution rule NotT is not applicable to sequent " + p.root.toString + " at index "+ index)
      }
    }
    def unapply(proof: ResolutionProof[LabeledSequent]) = if (proof.rule == NotTType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[LabeledSequent] with LiteralId]
        Some((pr.root, pr.uProof, pr.literalId))
    }
  }
  object NotF {
    def apply(p: ResolutionProof[LabeledSequent], index: Int): ResolutionProof[LabeledSequent] = {
      val pair = p.root.getAntecedentPairAtIndex(index)
      pair._1._1 match {
        case Neg(f) => new UnaryAGraph[LabeledSequent](LabeledSequent(pair._2, (f,pair._1._2) :: p.root.succedentLabeled), p)
          with UnaryResolutionProof[LabeledSequent] with LiteralId {def rule = NotFType; def literalId = index}
        case _ => throw new RuleException("Andrews resolution rule NotF is not applicable to sequent " + p.root.toString + " at index "+ index)
      }
    }
    def unapply(proof: ResolutionProof[LabeledSequent]) = if (proof.rule == NotFType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[LabeledSequent] with LiteralId]
        Some((pr.root, pr.uProof, pr.literalId))
    }
  }

  object OrT {
    def apply(p: ResolutionProof[LabeledSequent], index: Int): ResolutionProof[LabeledSequent] = {
      val pair = p.root.getSuccedentPairAtIndex(index)
      pair._1._1 match {
        case Or(a,b) => new UnaryAGraph[LabeledSequent](LabeledSequent(p.root.antecedentLabeled, (a,pair._1._2) :: (b,pair._1._2) :: pair._2), p)
          with UnaryResolutionProof[LabeledSequent] with LiteralId {def rule = OrTType; def literalId = index}
        case _ => throw new RuleException("Andrews resolution rule OrT is not applicable to sequent " + p.root.toString + " at index "+ index)
      }
    }
    def unapply(proof: ResolutionProof[LabeledSequent]) = if (proof.rule == OrTType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[LabeledSequent] with LiteralId]
        Some((pr.root, pr.uProof, pr.literalId))
    }
  }
  object OrFL {
    def apply(p: ResolutionProof[LabeledSequent], index: Int): ResolutionProof[LabeledSequent] = {
      val pair = p.root.getAntecedentPairAtIndex(index)
      pair._1._1 match {
        case Or(a,_) => new UnaryAGraph[LabeledSequent](LabeledSequent((a,pair._1._2) :: pair._2, p.root.succedentLabeled), p)
          with UnaryResolutionProof[LabeledSequent] with LiteralId {def rule = OrFLType; def literalId = index}
        case _ => throw new RuleException("Andrews resolution rule OrFL is not applicable to sequent " + p.root.toString + " at index "+ index)
      }
    }
    def unapply(proof: ResolutionProof[LabeledSequent]) = if (proof.rule == OrFLType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[LabeledSequent] with LiteralId]
        Some((pr.root, pr.uProof, pr.literalId))
    }
  }
  object OrFR {
    def apply(p: ResolutionProof[LabeledSequent], index: Int): ResolutionProof[LabeledSequent] = {
      val pair = p.root.getAntecedentPairAtIndex(index)
      pair._1._1 match {
        case Or(_,b) => new UnaryAGraph[LabeledSequent](LabeledSequent((b,pair._1._2) :: pair._2, p.root.succedentLabeled), p)
          with UnaryResolutionProof[LabeledSequent] with LiteralId {def rule = OrFRType; def literalId = index}
        case _ => throw new RuleException("Andrews resolution rule OrFR is not applicable to sequent " + p.root.toString + " at index "+ index)
      }
    }
    def unapply(proof: ResolutionProof[LabeledSequent]) = if (proof.rule == OrFRType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[LabeledSequent] with LiteralId]
        Some((pr.root, pr.uProof, pr.literalId))
    }
  }

  object ForallT {
    def apply(p: ResolutionProof[LabeledSequent], index: Int, term: HOLExpression): ResolutionProof[LabeledSequent] = {
      val pair = p.root.getSuccedentPairAtIndex(index)
      pair._1._1 match {
        case All( sub, v ) => new UnaryAGraph[LabeledSequent](LabeledSequent(p.root.antecedentLabeled, (betaNormalize(App( sub, term )).asInstanceOf[HOLFormula], new Labeled[List[HOLExpression]] {val label = term :: pair._1._2.label}) :: pair._2), p)
          with UnaryResolutionProof[LabeledSequent] with LiteralId with InstantiatedVariable {def rule = AllTType; def literalId = index; def term = term}
        case _ => throw new RuleException("Andrews resolution rule AllTType is not applicable to sequent " + p.root.toString + " at index "+ index)
      }
    }
    def unapply(proof: ResolutionProof[LabeledSequent]) = if (proof.rule == AllTType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[LabeledSequent] with LiteralId with InstantiatedVariable]
        Some((pr.root, pr.uProof, pr.literalId, pr.term))
    }
  }

  object ForallF {
    def apply(p: ResolutionProof[LabeledSequent], index: Int, term: HOLExpression): ResolutionProof[LabeledSequent] = {
      val pair = p.root.getAntecedentPairAtIndex(index)
      pair._1._1 match {
        case All( sub, v ) => new UnaryAGraph[LabeledSequent](LabeledSequent((betaNormalize(App( sub, term )).asInstanceOf[HOLFormula], pair._1._2) :: pair._2, p.root.succedentLabeled), p)
          with UnaryResolutionProof[LabeledSequent] with LiteralId with InstantiatedVariable {def rule = AllFType; def literalId = index; def term = term}
        case _ => throw new RuleException("Andrews resolution rule AllF is not applicable to sequent " + p.root.toString + " at index "+ index)
      }
    }
    def unapply(proof: ResolutionProof[LabeledSequent]) = if (proof.rule == AllFType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[LabeledSequent] with LiteralId with InstantiatedVariable]
        Some((pr.root, pr.uProof, pr.literalId, pr.term))
    }
  }

  object Sub {
    def apply[T <: LambdaExpression](p: ResolutionProof[LabeledSequent], sub: Substitution[T]): ResolutionProof[LabeledSequent] = {
      new UnaryAGraph[LabeledSequent](LabeledSequent(
          p.root.antecedentLabeled.map(x => (sub(x._1.asInstanceOf[T]).asInstanceOf[HOLFormula], new Labeled[List[HOLExpression]] {val label = x._2.label.map(y => sub(y.asInstanceOf[T]).asInstanceOf[HOLFormula])})),
          p.root.succedentLabeled.map(x => (sub(x._1.asInstanceOf[T]).asInstanceOf[HOLFormula], new Labeled[List[HOLExpression]] {val label = x._2.label.map(y => sub(y.asInstanceOf[T]).asInstanceOf[HOLFormula])}))),
        p)
          with UnaryResolutionProof[LabeledSequent] with AppliedSubstitution[T] {def rule = SubType; def substitution = sub}
    }
    def unapply[T <: LambdaExpression](proof: ResolutionProof[LabeledSequent] with AppliedSubstitution[T]) = if (proof.rule == SubType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[LabeledSequent] with AppliedSubstitution[T]]
        Some((pr.root, pr.uProof, pr.substitution))
    }
  }
}