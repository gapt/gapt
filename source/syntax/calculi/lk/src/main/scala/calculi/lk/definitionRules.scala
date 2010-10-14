/*
 * definitionRules.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.utils.ds.acyclicGraphs._
import base._

package definitionRules {
import at.logic.utils.ds.acyclicGraphs._

// Definition rules
  case object DefinitionLeftRuleType extends UnaryRuleTypeA
  case object DefinitionRightRuleType extends UnaryRuleTypeA

  // TODO: implement verification of the rule
  object DefinitionLeftRule {
    def apply(s1: LKProof, term1oc: Occurrence, main: HOLFormula) = {
      val term1op = s1.root.antecedent.find(_ == term1oc)
      if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val aux_fo = term1op.get
        val prinFormula = aux_fo.factory.createPrincipalFormulaOccurrence(main, aux_fo::Nil, s1.root.antecedent - aux_fo)
        new UnaryAGraph[SequentOccurrence](
            SequentOccurrence(createContext((s1.root.antecedent - aux_fo)) + prinFormula,
                              createContext((s1.root.succedent))), s1 )
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = DefinitionLeftRuleType
          def aux = (aux_fo::Nil)::Nil
          def prin = prinFormula::Nil
        }
      }
    }

    def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula): UnaryAGraph[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas =
      s1.root.antecedent.filter( x => x.formula == aux ).toList match {
        case (x::_) => apply( s1, x, main )
        case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
      }

    def unapply(proof: LKProof) = if (proof.rule == DefinitionLeftRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }

  // TODO: implement verification of the rule
  object DefinitionRightRule {
    def apply(s1: LKProof, term1oc: Occurrence, main: HOLFormula) = {
      val term1op = s1.root.succedent.find(_ == term1oc)
      if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val aux_fo = term1op.get
        val prinFormula = aux_fo.factory.createPrincipalFormulaOccurrence(main, aux_fo::Nil, s1.root.succedent - aux_fo)
        new UnaryAGraph[SequentOccurrence](
            SequentOccurrence(createContext(s1.root.antecedent),
                              createContext((s1.root.succedent - aux_fo)) + prinFormula), s1 )
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = DefinitionRightRuleType
          def aux = (aux_fo::Nil)::Nil
          def prin = prinFormula::Nil
        }
      }
    }

    def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula): UnaryAGraph[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas =
      s1.root.succedent.filter( x => x.formula == aux ).toList match {
        case (x::_) => apply( s1, x, main )
        case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
      }

    def unapply(proof: LKProof) = if (proof.rule == DefinitionRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }
}
