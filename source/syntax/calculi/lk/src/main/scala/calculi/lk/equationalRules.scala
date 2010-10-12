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
import at.logic.utils.ds.acyclicGraphs._
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
    def apply(s1: LKProof, s2: LKProof, eqocc: FormulaOccurrence, auxocc: FormulaOccurrence, main: HOLFormula) =
      if (!s1.root.succedent.contains(eqocc) || !s2.root.antecedent.contains(auxocc)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val prinFormula = eqocc.factory.createPrincipalFormulaOccurrence(main, eqocc::auxocc::Nil)
        new BinaryAGraph[SequentOccurrence](
            SequentOccurrence(createContext((s1.root.antecedent) ++ s2.root.antecedent - auxocc) + prinFormula,
                              createContext((s1.root.succedent - eqocc) ++ s2.root.succedent) ), s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationLeft1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
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
    def apply(s1: LKProof, s2: LKProof, eqocc: FormulaOccurrence, auxocc: FormulaOccurrence, main: HOLFormula) =
      if (!s1.root.succedent.contains(eqocc) || !s2.root.antecedent.contains(auxocc)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val prinFormula = eqocc.factory.createPrincipalFormulaOccurrence(main, eqocc::auxocc::Nil)
        new BinaryAGraph[SequentOccurrence](
            SequentOccurrence(createContext((s1.root.antecedent) ++ s2.root.antecedent - auxocc) + prinFormula,
                              createContext((s1.root.succedent - eqocc) ++ s2.root.succedent) ), s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationLeft1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
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
    def apply(s1: LKProof, s2: LKProof, eqocc: FormulaOccurrence, auxocc: FormulaOccurrence, main: HOLFormula) =
      if (!s1.root.succedent.contains(eqocc) || !s2.root.succedent.contains(auxocc)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val prinFormula = eqocc.factory.createPrincipalFormulaOccurrence(main, eqocc::auxocc::Nil)
        new BinaryAGraph[SequentOccurrence](
            SequentOccurrence(createContext(s1.root.antecedent ++ s2.root.antecedent),
                              createContext((s1.root.succedent - eqocc) ++ (s2.root.succedent - auxocc)) + prinFormula ),
            s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationRight1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
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
    def apply(s1: LKProof, s2: LKProof, eqocc: FormulaOccurrence, auxocc: FormulaOccurrence, main: HOLFormula) =
      if (!s1.root.succedent.contains(eqocc) || !s2.root.succedent.contains(auxocc)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val prinFormula = eqocc.factory.createPrincipalFormulaOccurrence(main, eqocc::auxocc::Nil)
        new BinaryAGraph[SequentOccurrence](
            SequentOccurrence(createContext(s1.root.antecedent ++ s2.root.antecedent),
                              createContext((s1.root.succedent - eqocc) ++ (s2.root.succedent - auxocc)) + prinFormula),
            s1, s2 )
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = EquationRight1RuleType
          def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
          def prin = prinFormula::Nil
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
