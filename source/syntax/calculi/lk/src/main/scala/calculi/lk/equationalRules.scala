/*
 * equationalRules.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap
import base._
import at.logic.utils.traits.Occurrence

package equationalRules {

  // Definition rules
  case object EquationLeft1RuleType extends BinaryRuleTypeA
  case object EquationLeft2RuleType extends BinaryRuleTypeA
  case object EquationRight1RuleType extends BinaryRuleTypeA
  case object EquationRight2RuleType extends BinaryRuleTypeA

  // TODO: implement verification of the rule
  object EquationLeft1Rule {
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val term1op = s1.root.succedent.find(_ == term1oc)
      val term2op = s2.root.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        val prinFormula = FormulaOccurrence(main, eqocc::auxocc::Nil)
        new BinaryTree[Sequent](
            Sequent(createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent.filterNot(_ == auxocc)) :+ prinFormula,
                              createContext(s1.root.succedent.filterNot(_ == eqocc)) ++ createContext(s2.root.succedent) ), s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationLeft1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "e:l1"
        }
      }
    }

    // convenient method to use formulas
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == EquationLeft1RuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, p1))
      }
      else None
  }

  // TODO: implement verification of the rule
  object EquationLeft2Rule {
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val term1op = s1.root.succedent.find(_ == term1oc)
      val term2op = s2.root.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        val prinFormula = FormulaOccurrence(main, eqocc::auxocc::Nil)
        new BinaryTree[Sequent](
            Sequent(createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent.filterNot(_ == auxocc)) :+ prinFormula,
                              createContext(s1.root.succedent.filterNot(_ == eqocc)) ++ createContext(s2.root.succedent) ), s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationLeft1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "e:l2"
        }
      }
    }

    // convenient method to use formulas
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == EquationLeft2RuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, p1))
      }
      else None
  }

  // TODO: implement verification of the rule
  object EquationRight1Rule {
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val term1op = s1.root.succedent.find(_ == term1oc)
      val term2op = s2.root.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        val prinFormula = FormulaOccurrence(main, eqocc::auxocc::Nil)
        new BinaryTree[Sequent](
            Sequent(createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent),
                              createContext(s1.root.succedent.filterNot(_ == eqocc)) ++ createContext(s2.root.succedent.filterNot(_ == auxocc)) :+ prinFormula ),
            s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationRight1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "e:r1"
        }
      }
    }

    // convenient method to use formulas
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.succedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == EquationRight1RuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, p1))
      }
      else None
  }

  // TODO: implement verification of the rule
  object EquationRight2Rule {
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val term1op = s1.root.succedent.find(_ == term1oc)
      val term2op = s2.root.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        val prinFormula = FormulaOccurrence(main, eqocc::auxocc::Nil)
        new BinaryTree[Sequent](
            Sequent(createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent),
                              createContext(s1.root.succedent.filterNot(_ == eqocc)) ++ createContext(s2.root.succedent.filterNot(_ == auxocc)) :+ prinFormula),
            s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationRight1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "e:r2"
        }
      }
    }

    // convenient method to use formulas
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.succedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == EquationRight2RuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, p1))
      }
      else None
  }
}
