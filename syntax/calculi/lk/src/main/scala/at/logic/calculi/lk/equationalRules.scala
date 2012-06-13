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
      val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.root.antecedent)
      val ant2 = createContext(s2.root.antecedent.filterNot(_ == auxocc))
      val antecedent = ant1 ++ ant2 :+ prinFormula
      val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.root.succedent)
      val succedent = suc1 ++ suc2

      new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2 )
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = EquationLeft1RuleType
        def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "e:l1"
      }
    }
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent.filterNot(_ == auxocc))
      val antecedent = ant1 ++ ant2 :+ prinFormula
      val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.succedent)
      val succedent = suc1 ++ suc2

      Sequent(antecedent, succedent)
    }
    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        (eqocc, auxocc)
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
      val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.root.antecedent)
      val ant2 = createContext(s2.root.antecedent.filterNot(_ == auxocc))
      val antecedent = ant1 ++ ant2 :+ prinFormula
      val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.root.succedent)
      val succedent = suc1 ++ suc2

      new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2 )
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = EquationLeft2RuleType
        def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "e:l2"
      }
    }
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent.filterNot(_ == auxocc))
      val antecedent = ant1 ++ ant2 :+ prinFormula
      val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.succedent)
      val succedent = suc1 ++ suc2

      Sequent(antecedent, succedent)
    }
    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        (eqocc, auxocc)
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
      val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.root.antecedent)
      val ant2 = createContext(s2.root.antecedent)
      val antecedent = ant1 ++ ant2
      val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.root.succedent.filterNot(_ == auxocc))
      val succedent = suc1 ++ suc2 :+ prinFormula

      new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2 )
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = EquationRight1RuleType
        def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "e:r1"
      }
    }
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent)
      val antecedent = ant1 ++ ant2
      val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.succedent.filterNot(_ == auxocc))
      val succedent = suc1 ++ suc2 :+ prinFormula

      Sequent(antecedent, succedent)
    }
    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        (eqocc, auxocc)
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
      val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.root.antecedent)
      val ant2 = createContext(s2.root.antecedent)
      val antecedent = ant1 ++ ant2
      val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.root.succedent.filterNot(_ == auxocc))
      val succedent = suc1 ++ suc2 :+ prinFormula

      new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2 )
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = EquationRight2RuleType
        def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "e:r2"
      }
    }
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent)
      val antecedent = ant1 ++ ant2
      val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.succedent.filterNot(_ == auxocc))
      val succedent = suc1 ++ suc2 :+ prinFormula

      Sequent(antecedent, succedent)
    }
    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        (eqocc, auxocc)
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
