/*
 * propositionalRules.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lksk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol.propositions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.{Set,EmptySet}
import scala.collection.mutable.{Map,HashMap}
import base._
import base.TypeSynonyms._

import at.logic.calculi.lk.base.{LKFOFactory,Sequent,AuxiliaryFormulas,PrincipalFormulas}
import at.logic.calculi.lk.propositionalRules.{InitialRuleType, WeakeningLeftRuleType, WeakeningRightRuleType, ContractionLeftRuleType, ContractionRightRuleType, CutRuleType, AndRightRuleType, AndLeft1RuleType, AndLeft2RuleType, OrRight1RuleType, OrRight2RuleType, OrLeftRuleType, ImpRightRuleType, ImpLeftRuleType, NegLeftRuleType, NegRightRuleType}
import at.logic.calculi.lk.propositionalRules.{Axiom => LKAxiom}

package propositionalRules {

  // lksk proofs
  // rules are extracted in the form (UpperSequent(s), LowerSequent, AuxialiaryFormula(s), PrincipalFormula(s))

  // actual rule extractor/factories
  // Axioms (and weakenings) always return a pair(Proof, mapping) which maps the indices of the list given into the new occurrences.
  object Axiom {
    def apply(seq: Sequent, maps: Pair[List[Label], List[Label]]): Pair[LKskProof, Pair[List[FormulaOccurrence],List[FormulaOccurrence]]] = {
      val left: List[FormulaOccurrence] = seq.antecedent.map(createOccurrence)
      val right: List[FormulaOccurrence] = seq.succedent.map(createOccurrence)
      (new LeafTree[LabelledSequentOccurrence](LabelledSequentOccurrence(LKAxiom.toSet(left), LKAxiom.toSet(right), createLabelMap( left, right, maps ))) with LKskProof {def rule = InitialRuleType}, (left,right))
    }
    def createOccurrence(f: Formula): FormulaOccurrence = LKFOFactory.createOccurrence(f, Nil)
    def createLabelMap(left: List[FormulaOccurrence], right: List[FormulaOccurrence], maps: Pair[List[Label], List[Label]]) : Map[FormulaOccurrence,Label] =
    {
      val m = new HashMap[FormulaOccurrence,Label]
      left.zip(left.indices).foreach( p => m.update( p._1, maps._1.apply( p._2 ) ) )
      right.zip(right.indices).foreach( p => m.update( p._1, maps._2.apply( p._2 ) ) )
      m
    }
    def unapply(proof: LKskProof) = if (proof.rule == InitialRuleType) Some((proof.root)) else None
  }

  object OrLeftRule {
    def apply(s1: LKskProof, s2: LKskProof, term1: FormulaOccurrence, term2: FormulaOccurrence) = {
      if (!s1.root.antecedent.contains(term1) || !s2.root.antecedent.contains(term2)) throw new LKskRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else if (s1.root.map.apply(term1) != s2.root.map.apply(term2)) throw new LKskRuleCreationException("Labels of auxiliary formulas do not coincide")
      else {
        val prinFormula = term1.factory.createPrincipalFormulaOccurrence(Or(term1.formula, term2.formula), term1::term2::Nil)
        val prinmap = new HashMap[FormulaOccurrence,Label]
        prinmap.update( prinFormula, s1.root.map(term1) )
        val prinseq = LabelledSequentOccurrence( new EmptySet + prinFormula, new EmptySet, prinmap )
        val ant = createLeftContext(s1.root.antecedent - term1, s1.root.map) ++ createLeftContext(s2.root.antecedent - term2, s2.root.map)
        val suc = createRightContext(s1.root.succedent ++ s2.root.succedent, s1.root.map ++ s2.root.map)
        new BinaryTree[LabelledSequentOccurrence]( prinseq ++ ant ++ suc, s1, s2 )
          with BinaryLKskProof with AuxiliaryFormulas with PrincipalFormulas {
            def rule = OrLeftRuleType
            def aux = ((term1)::Nil)::(term2::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
    }
    
    // convenient method to choose the first two formulas
    def apply(s1: LKskProof, s2: LKskProof, term1: Formula, term2: Formula): BinaryTree[LabelledSequentOccurrence] with BinaryLKskProof with AuxiliaryFormulas with PrincipalFormulas
    = {
      ((s1.root.antecedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y)
        case _ => throw new LKskRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }

    def unapply(proof: LKskProof) = if (proof.rule == OrLeftRuleType) {
        val r = proof.asInstanceOf[BinaryLKskProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, a1, a2, p1))
      }
      else None
  }
}
