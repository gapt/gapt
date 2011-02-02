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

package equationalRules {

  // Definition rules
  case object EquationLeft1RuleType extends BinaryRuleTypeA
  case object EquationLeft2RuleType extends BinaryRuleTypeA
  case object EquationRight1RuleType extends BinaryRuleTypeA
  case object EquationRight2RuleType extends BinaryRuleTypeA

  // TODO: implement verification of the rule
  object EquationLeft1Rule {
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val term1op = s1.root.succedent.find(x => x == term1oc)
      val term2op = s2.root.antecedent.find(x => x == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        val prinFormula = eqocc.factory.createPrincipalFormulaOccurrence(main, eqocc::auxocc::Nil, (s1.root.antecedent) ++ s2.root.antecedent - auxocc)
        new BinaryTree[SequentOccurrence](
            SequentOccurrence(createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent - auxocc, s1.root.antecedent) + prinFormula,
                              createContext(s1.root.succedent - eqocc) ++ createContext(s2.root.succedent, s1.root.succedent - eqocc) ), s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationLeft1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "e:l1"
        }
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
      val term1op = s1.root.succedent.find(x => x == term1oc)
      val term2op = s2.root.antecedent.find(x => x == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        val prinFormula = eqocc.factory.createPrincipalFormulaOccurrence(main, eqocc::auxocc::Nil, s1.root.antecedent ++ s2.root.antecedent - auxocc)
        new BinaryTree[SequentOccurrence](
            SequentOccurrence(createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent - auxocc, s1.root.antecedent) + prinFormula,
                              createContext(s1.root.succedent - eqocc) ++ createContext(s2.root.succedent, s1.root.succedent - eqocc) ), s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationLeft1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "e:l2"
        }
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
      val term1op = s1.root.succedent.find(x => x == term1oc)
      val term2op = s2.root.succedent.find(x => x == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        val prinFormula = eqocc.factory.createPrincipalFormulaOccurrence(main, eqocc::auxocc::Nil, (s1.root.succedent - eqocc) ++ (s2.root.succedent - auxocc))
        new BinaryTree[SequentOccurrence](
            SequentOccurrence(createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent, s1.root.antecedent),
                              createContext(s1.root.succedent - eqocc) ++ createContext(s2.root.succedent - auxocc, s1.root.succedent - eqocc) + prinFormula ),
            s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationRight1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "e:r1"
        }
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
      val term1op = s1.root.succedent.find(x => x == term1oc)
      val term2op = s2.root.succedent.find(x => x == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        val prinFormula = eqocc.factory.createPrincipalFormulaOccurrence(main, eqocc::auxocc::Nil, (s1.root.succedent - eqocc) ++ (s2.root.succedent - auxocc))
        new BinaryTree[SequentOccurrence](
            SequentOccurrence(createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent, s1.root.antecedent),
                              createContext(s1.root.succedent - eqocc) ++ createContext(s2.root.succedent - auxocc, s1.root.succedent - eqocc) + prinFormula),
            s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationRight1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "e:r2"
        }
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
