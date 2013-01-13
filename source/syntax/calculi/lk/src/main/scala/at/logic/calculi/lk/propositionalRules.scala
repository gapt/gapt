/*
 * LK.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.utils.traits.Occurrence
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.utils.ds.trees._
import base._

package propositionalRules {

import collection.immutable.Seq

  // axioms
  case object InitialRuleType extends NullaryRuleTypeA

  // structural rules
  case object WeakeningLeftRuleType extends UnaryRuleTypeA
  case object WeakeningRightRuleType extends UnaryRuleTypeA
  case object ContractionLeftRuleType extends UnaryRuleTypeA
  case object ContractionRightRuleType extends UnaryRuleTypeA
  case object CutRuleType extends BinaryRuleTypeA

  // Propositional rules
  case object AndRightRuleType extends BinaryRuleTypeA
  case object AndLeft1RuleType extends UnaryRuleTypeA
  case object AndLeft2RuleType extends UnaryRuleTypeA
  case object OrRight1RuleType extends UnaryRuleTypeA
  case object OrRight2RuleType extends UnaryRuleTypeA
  case object OrLeftRuleType extends BinaryRuleTypeA
  case object ImpRightRuleType extends UnaryRuleTypeA
  case object ImpLeftRuleType extends BinaryRuleTypeA
  case object NegLeftRuleType extends UnaryRuleTypeA
  case object NegRightRuleType extends UnaryRuleTypeA


  // lk proofs
  // rules are extracted in the form (UpperSequent(s), LowerSequent, AuxiliaryFormula(s), PrincipalFormula(s))

  // actual rule extractor/factories
  // Axioms (and weakenings) always return a pair(Proof, mapping) which maps the indices of the list given into the new occurrences.
  // It is used together with an implicit conversion between this pair into a proof so users who are not interested in this information will not see it

  object Axiom {
    def apply(seq: Sequent) : LeafTree[Sequent] with NullaryLKProof = {
      if (seq.antecedent.exists((fo:FormulaOccurrence) => (fo.ancestors.size > 0) ))
        throw new LKRuleCreationException("Ancestor of an occurence in antecedent of Axiom rule is nonempty!")
      if (seq.succedent.exists((fo:FormulaOccurrence) => (fo.ancestors.size > 0) ))
        throw new LKRuleCreationException("Ancestor of an occurence in succedent of Axiom rule is nonempty!")

      new LeafTree[Sequent](seq) with NullaryLKProof {def rule = InitialRuleType}
    }
    def apply[T](ant: Seq[Formula], suc: Seq[Formula]) (implicit factory: FOFactory) = {
      val left: Seq[FormulaOccurrence] = ant.map(x => factory.createFormulaOccurrence(x.asInstanceOf[HOLFormula], Nil))
      val right: Seq[FormulaOccurrence] = suc.map(x => factory.createFormulaOccurrence(x.asInstanceOf[HOLFormula], Nil))
      new LeafTree[Sequent](Sequent(left, right)) with NullaryLKProof {def rule = InitialRuleType}
    }
    def unapply(proof: LKProof) = if (proof.rule == InitialRuleType) Some((proof.root)) else None
  }

  object WeakeningLeftRule {
    def apply(s1: LKProof, f: HOLFormula) (implicit factory: FOFactory) = {
      val prinFormula = getPrinFormula(f)
      val sequent = getSequent(s1.root, prinFormula)
      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with PrincipalFormulas {
          def rule = WeakeningLeftRuleType
          def prin = prinFormula::Nil
          override def name = "w:l"
        }
    }
    def apply(s1 : Sequent, f : HOLFormula)(implicit factory : FOFactory) = {
      val prinFormula = getPrinFormula(f)
      getSequent(s1, prinFormula)
    }
    private def getPrinFormula(f: HOLFormula) = {
      factory.createFormulaOccurrence(f, Nil)
    }
    private def getSequent(s1: Sequent, prinFormula: FormulaOccurrence) = {
      Sequent(createContext(s1.antecedent) :+ prinFormula, createContext(s1.succedent))
    }
    def unapply(proof: LKProof) = if (proof.rule == WeakeningLeftRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with PrincipalFormulas]
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, p1))
      }
      else None
  }

  object WeakeningRightRule {
    def apply(s1: LKProof, f: HOLFormula) (implicit factory: FOFactory) = {
      val prinFormula = getPrinFormula(f)
      val sequent = getSequent(s1.root, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with PrincipalFormulas {
          def rule = WeakeningRightRuleType
          def prin = prinFormula::Nil
          override def name = "w:r"
        }
    }
    def apply(s1 : Sequent, f : HOLFormula)(implicit factory : FOFactory) = {
      val prinFormula = getPrinFormula(f)
      getSequent(s1, prinFormula)
    }
    private def getPrinFormula(f: HOLFormula) = {
      factory.createFormulaOccurrence(f, Nil)
    }
    private def getSequent(s1: Sequent, prinFormula: FormulaOccurrence) = {
      Sequent(createContext(s1.antecedent), createContext(s1.succedent) :+ prinFormula)
    }
    def unapply(proof: LKProof) = if (proof.rule == WeakeningRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with PrincipalFormulas]
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, p1))
      }
      else None
  }

  object ContractionLeftRule {
    def apply(s1: LKProof, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1.root, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      val sequent = getSequent(s1.root, term1, term2, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = ContractionLeftRuleType
          def aux = (term1::term2::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "c:l"
        }
    }
    def apply(s1: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, term1, term2, prinFormula)
    }
    // convenient method to choose the first two formulas
    def apply(s1: LKProof, term1: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
      (s1.root.antecedent.filter(x => x.formula == term1)).toList match {
        case (x::y::_) => apply(s1, x, y)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found in " + s1.root.antecedent.map(_.formula) +
          " for application of the rule with the given formula: " + term1)
      }
    }
    private def getTerms(s1: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.antecedent.find(_ == term1oc)
      val term2op = s1.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the left part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        if (term1.formula != term2.formula) throw new LKRuleCreationException("Formulas to be contracted are not identical: term1.formula = " + term1.formula.toStringSimple + ", term2.formula = " + term2.formula.toStringSimple)
        else if (term1 == term2) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
        else {
          (term1, term2)
        }
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
      term1.factory.createFormulaOccurrence(holterm1, term1::term2::Nil)
    }
    private def getSequent(s1: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val ant1 = createContext(s1.antecedent.filterNot(x => x == term1 || x == term2))
      val antecedent = ant1 :+ prinFormula
      val succedent = createContext(s1.succedent)
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == ContractionLeftRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::a2::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, a2, p1))
      }
      else None
  }

  object ContractionRightRule {
    def apply(s1: LKProof, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1.root, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      val sequent = getSequent(s1.root, term1, term2, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = ContractionRightRuleType
          def aux = (term1::term2::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "c:r"
        }
    }
    def apply(s1: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, term1, term2, prinFormula)
    }
    // convenient method to choose the first two formulas
    def apply(s1: LKProof, term1: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
      (s1.root.succedent.filter(x => x.formula == term1)).toList match {
        case (x::y::_) => apply(s1, x, y)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found in " + s1.root.succedent.map(_.formula) +
          " for application of the rule with the given formula: " + term1)
      }
    }
    private def getTerms(s1 : Sequent, term1oc : Occurrence, term2oc : Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s1.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        if (term1.formula != term2.formula) throw new LKRuleCreationException("Formulas to be contracted are not identical: term1.formula = " + term1.formula.toStringSimple + ", term2.formula = " + term2.formula.toStringSimple)
        else if (term1 == term2) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
        else {
          (term1, term2)
        }
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
      term1.factory.createFormulaOccurrence(holterm1, term1::term2::Nil)
    }
    private def getSequent(s1: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val antecedent = createContext(s1.antecedent)
      val suc1 = createContext(s1.succedent.filterNot(x =>  x == term1 || x == term2))
      val succedent = suc1 :+ prinFormula
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == ContractionRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::a2::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, a2, p1))
      }
      else None
  }

  object CutRule {
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val sequent = getSequent(s1.root, s2.root, term1, term2)

      new BinaryTree[Sequent](sequent, s1, s2)
        with BinaryLKProof with AuxiliaryFormulas {
            def rule = CutRuleType
            def aux = (term1::Nil)::(term2::Nil)::Nil
            override def name = "cut"
        }
    }
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1, s2, term1oc, term2oc)
      getSequent(s1, s2, term1, term2)
    }
     // convenient method to choose the first two formulas
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas  = {
      ((s1.root.succedent.filter(x => x.formula.syntaxEquals(term1))).toList,(s2.root.antecedent.filter(x => x.formula.syntaxEquals(term1))).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y)
        case (Nil,Nil) =>throw new LKRuleCreationException("Not matching formula occurrences found in both " + s1.root.succedent + " and " +
          s2.root.antecedent + " for application of the rule with the given formula " + term1)
        case (Nil,_) =>throw new LKRuleCreationException("Not matching formula occurrences found in " + s1.root.succedent +
          " for application of the rule with the given formula " + term1)
        case (_,Nil) =>throw new LKRuleCreationException("Not matching formula occurrences found in " + s2.root.antecedent +
          " for application of the rule with the given formula " + term1)
      }
    }
    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) {
        val s1str = s1.succedent.head.toString()
        val s2str = s2.antecedent.head.toString()
        val t1str = term1oc.asInstanceOf[FormulaOccurrence].formula.toString()
        val t2str = term2oc.asInstanceOf[FormulaOccurrence].formula.toString()
        val str = "s1: " + s1str + "\ns2: " + s2str + "\nt1: " + t1str + "\nt2: " + t2str + "\n"
        throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent\n" + str)
      }
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        if (!term1.formula.syntaxEquals(term2.formula)) throw new LKRuleCreationException("Formulas to be cut are not identical")
        else {
          (term1, term2)
        }
      }
    }
    private def getSequent(s1: Sequent, s2: Sequent, term1: Occurrence, term2: Occurrence) = {
      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent.filterNot(_ == term2))
      val antecedent = ant1 ++ ant2
      val suc1 = createContext(s1.succedent.filterNot(_ == term1))
      val suc2 = createContext(s2.succedent)
      val succedent = suc1 ++ suc2
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == CutRuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas]
        val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
        Some((r.uProof1, r.uProof2, r.root, a1, a2))
      }
      else None
  }

  object AndRightRule {
    def computeLeftAux( main: HOLFormula ) = main match { case And(l, _) => l }

    def computeRightAux( main: HOLFormula ) = main match { case And(_, r) => r }

    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      val sequent = getSequent(s1.root, s2.root, term1, term2, prinFormula)

      new BinaryTree[Sequent](sequent, s1, s2)
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = AndRightRuleType
          def aux = ((term1)::Nil)::(term2::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2227:r"
        }
    }
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, s2, term1, term2, prinFormula)
    }
    // convenient method to choose the first two formulas
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula): BinaryLKProof with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.succedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        (term1, term2)
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
      val holterm2 = term2.formula.asInstanceOf[HOLFormula]
      val form = And(holterm1, holterm2)
      term1.factory.createFormulaOccurrence(form, term1::term2::Nil)
    }
    private def getSequent(s1: Sequent, s2: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent)
      val antecedent = ant1 ++ ant2
      val suc1 = createContext(s1.succedent.filterNot(_ == term1))
      val suc2 = createContext(s2.succedent.filterNot(_ == term2))
      val succedent = suc1 ++ suc2 :+ prinFormula
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == AndRightRuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, a1, a2, p1))
      }
      else None
  }

  object AndLeft1Rule {
    def computeAux( main: HOLFormula ) = main match { case And(l, _) => l }

    def apply(s1: LKProof, term1oc: Occurrence, term2: HOLFormula) = {
      val term1 = getTerms(s1.root, term1oc)
      val prinFormula = getPrinFormula(term1, term2)
      val sequent = getSequent(s1.root, term1, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = AndLeft1RuleType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2227:l1"
        }
    }
    def apply(s1: Sequent, term1oc: Occurrence, term2: HOLFormula) = {
      val term1 = getTerms(s1, term1oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, term1, prinFormula)
    }
    // convenient method to choose the first  formula
    def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      (s1.root.antecedent.filter(x => x.formula == term1)).toList match {
        case (x::_) => apply(s1, x, term2)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, term1oc: Occurrence) = {
      val term1op = s1.antecedent.find(_ == term1oc)
      if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the left part of the sequent")
      else {
        val term1 = term1op.get
        term1
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence, term2: HOLFormula) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
      val form = And(holterm1, term2)
      term1.factory.createFormulaOccurrence(form, term1::Nil)
    }
    private def getSequent(s1: Sequent, term1: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val antecedent = createContext(s1.antecedent.filterNot(_ == term1)) :+ prinFormula
      val succedent = createContext(s1.succedent)
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == AndLeft1RuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }

  object AndLeft2Rule {
    def computeAux( main: HOLFormula ) = main match { case And(_, r) => r }

    def apply(s1: LKProof, term1: HOLFormula, term2oc: Occurrence) = {
      val term2 = getTerms(s1.root, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      val sequent = getSequent(s1.root, term2, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = AndLeft2RuleType
          def aux = (term2::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2227:l2"
        }
    }
    def apply(s1: Sequent, term1: HOLFormula, term2oc: Occurrence) = {
      val term2 = getTerms(s1, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, term2, prinFormula)
    }
    // convenient method to choose the first  formula
    def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      (s1.root.antecedent.filter(x => x.formula == term2)).toList match {
        case (x::_) => apply(s1, term1, x)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, term2oc: Occurrence) = {
      val term2op = s1.antecedent.find(_ == term2oc)
      if (term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the left part of the sequent")
      else {
        val term2 = term2op.get
        term2
      }
    }
    private def getPrinFormula(term1: HOLFormula, term2: FormulaOccurrence) = {
      val holterm2 = term2.formula.asInstanceOf[HOLFormula]
      val form = And(term1, holterm2)
      term2.factory.createFormulaOccurrence(form, term2::Nil)
    }
    private def getSequent(s1: Sequent, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val antecedent = createContext(s1.antecedent.filterNot(_ == term2)) :+ prinFormula
      val succedent = createContext(s1.succedent)
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == AndLeft2RuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }

  object OrLeftRule {
    def computeLeftAux( main: HOLFormula ) = main match { case Or(l, _) => l }

    def computeRightAux( main: HOLFormula ) = main match { case Or(_, r) => r }

    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      val sequent = getSequent(s1.root, s2.root, term1, term2, prinFormula)

      new BinaryTree[Sequent](sequent, s1, s2)
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = OrLeftRuleType
          def aux = ((term1)::Nil)::(term2::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2228:l"
        }
    }
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, s2, term1, term2, prinFormula)
    }
    // convenient method to choose the first two formulas
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
      ((s1.root.antecedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y)
        case _ => throw new LKRuleCreationException("No matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.antecedent.find(_ == term1oc)
      val term2op = s2.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        (term1, term2)
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
      val holterm2 = term2.formula.asInstanceOf[HOLFormula]
      val form = Or(holterm1, holterm2)
      term1.factory.createFormulaOccurrence(form, term1::term2::Nil)
    }
    private def getSequent(s1: Sequent, s2: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val ant1 = createContext(s1.antecedent.filterNot(_ == term1))
      val ant2 = createContext(s2.antecedent.filterNot(_ == term2))
      val antecedent = ant1 ++ ant2 :+ prinFormula
      val succedent = createContext(s1.succedent) ++ createContext(s2.succedent)
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == OrLeftRuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, a1, a2, p1))
      }
      else None
  }

  object OrRight1Rule {
    def computeAux( main: HOLFormula ) = main match { case Or(l, _) => l }

    def apply(s1: LKProof, term1oc: Occurrence, term2: HOLFormula) = {
      val term1 = getTerms(s1.root, term1oc)
      val prinFormula = getPrinFormula(term1, term2)
      val sequent = getSequent(s1.root, term1, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = OrRight1RuleType
          def aux = ((term1)::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2228:r1"
        }
    }
    def apply(s1: Sequent, term1oc: Occurrence, term2: HOLFormula) = {
      val term1 = getTerms(s1, term1oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, term1, prinFormula)
    }
    // convenient method to choose the first  formula
    def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      (s1.root.succedent.filter(x => x.formula == term1)).toList match {
        case (x::_) => apply(s1, x, term2)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, term1oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      if (term1op == None) throw new LKRuleCreationException("Auxialiary formula is not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        term1
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence, term2: HOLFormula) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
      val form = Or(holterm1, term2)
      term1.factory.createFormulaOccurrence(form, term1::Nil)
    }
    private def getSequent(s1: Sequent, term1: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val antecedent = createContext(s1.antecedent)
      val suc1 = createContext(s1.succedent.filterNot(_ == term1))
      val succedent = suc1 :+ prinFormula
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == OrRight1RuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }

  object OrRight2Rule {
    def computeAux( main: HOLFormula ) = main match { case Or(_, r) => r }

    def apply(s1: LKProof, term1: HOLFormula, term2oc: Occurrence) = {
      val term2 = getTerms(s1.root, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      val sequent = getSequent(s1.root, term2, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = OrRight2RuleType
          def aux = ((term2)::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2228:r2"
        }
    }
    def apply(s1: Sequent, term1: HOLFormula, term2oc: Occurrence) = {
      val term2 = getTerms(s1, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, term2, prinFormula)
    }
    // convenient method to choose the first formula
    def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      (s1.root.succedent.filter(x => x.formula == term2)).toList match {
        case (x::_) => apply(s1, term1, x)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, term2oc: Occurrence) = {
      val term2op = s1.succedent.find(_ == term2oc)
      if (term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term2 = term2op.get
        term2
      }
    }
    private def getPrinFormula(term1: HOLFormula, term2: FormulaOccurrence) = {
      val holterm2 = term2.formula.asInstanceOf[HOLFormula]
      val form = Or(term1, holterm2)
      term2.factory.createFormulaOccurrence(form, term2::Nil)
    }
    private def getSequent(s1: Sequent, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val antecedent = createContext(s1.antecedent)
      val suc1 = createContext(s1.succedent.filterNot(_ == term2))
      val succedent = suc1 :+ prinFormula
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == OrRight2RuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }

  object ImpLeftRule {
    def computeLeftAux( main: HOLFormula ) = main match { case Imp(l, _) => l }

    def computeRightAux( main: HOLFormula ) = main match { case Imp(_, r) => r }

    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      val sequent = getSequent(s1.root, s2.root, term1, term2, prinFormula)

      new BinaryTree[Sequent](sequent, s1, s2)
        with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = ImpLeftRuleType
          def aux = (term1::Nil)::(term2::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2283:l"
        }
    }
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, s2, term1, term2, prinFormula)
    }
    // convenient method to choose the first two formulas
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        (term1, term2)
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
      val holterm2 = term2.formula.asInstanceOf[HOLFormula]
      val form = Imp(holterm1, holterm2)
      term1.factory.createFormulaOccurrence(form, term1::term2::Nil)
    }
    private def getSequent(s1: Sequent, s2: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent.filterNot(_ == term2))
      val antecedent = ant1 ++ ant2 :+ prinFormula
      val suc1 = createContext(s1.succedent.filterNot(_ == term1))
      val suc2 = createContext(s2.succedent)
      val succedent = suc1 ++ suc2
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == ImpLeftRuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, a1, a2, p1))
      }
      else None
  }

  object ImpRightRule {
    def apply(s1: LKProof, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1.root, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      val sequent = getSequent(s1.root, term1, term2, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = ImpRightRuleType
          def aux = (term1::term2::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2283:r"
        }
    }
    def apply(s1: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val (term1, term2) = getTerms(s1, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, term1, term2, prinFormula)
    }
    // convenient method to choose the first formula
    def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.antecedent.filter(x => x.formula == term1)).toList,(s1.root.succedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, x, y)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.antecedent.find(_ == term1oc)
      val term2op = s1.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        (term1, term2)
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
      val holterm2 = term2.formula.asInstanceOf[HOLFormula]
      val form = Imp(holterm1, holterm2)
      term1.factory.createFormulaOccurrence(form, term1::term2::Nil)
    }
    private def getSequent(s1: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val antecedent = createContext(s1.antecedent.filterNot(_ == term1))
      val suc1 = createContext(s1.succedent.filterNot(_ == term2))
      val succedent = suc1 :+ prinFormula
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == ImpRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::a2::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, a2, p1))
      }
      else None
  }

  object NegLeftRule {
    def computeAux( main: HOLFormula ) = main match { case Neg(s) => s }
    def apply(s1: LKProof, term1oc: Occurrence) = {
      val term1 = getTerms(s1.root, term1oc)
      val prinFormula = getPrinFormula(term1)
      val sequent = getSequent(s1.root, term1, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = NegLeftRuleType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u00ac:l"
        }

    }
    def apply(s1: Sequent, term1oc: Occurrence) = {
      val term1 = getTerms(s1, term1oc)
      val prinFormula = getPrinFormula(term1)
      getSequent(s1, term1, prinFormula)
    }
    // convenient method to choose the first formula
    def apply(s1: LKProof, term1: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      (s1.root.succedent.filter(x => x.formula == term1)).toList match {
        case (x::_) => apply(s1, x)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, term1oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        term1
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
      val form = Neg(holterm1)
      term1.factory.createFormulaOccurrence(form, term1::Nil)
    }
    private def getSequent(s1: Sequent, term1: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val antecedent = createContext(s1.antecedent) :+ prinFormula
      val succedent = createContext(s1.succedent.filterNot(_ == term1))
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == NegLeftRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }

  object NegRightRule {
    def computeAux( main: HOLFormula ) = main match { case Neg(s) => s }
    def apply(s1: LKProof, term1oc: Occurrence) = {
      val term1 = getTerms(s1.root, term1oc)
      val prinFormula = getPrinFormula(term1)
      val sequent = getSequent(s1.root, term1, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
          def rule = NegRightRuleType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u00ac:r"
        }

    }
    def apply(s1: Sequent, term1oc: Occurrence) = {
      val term1 = getTerms(s1, term1oc)
      val prinFormula = getPrinFormula(term1)
      getSequent(s1, term1, prinFormula)
    }
    // convenient method to choose the first formula
    def apply(s1: LKProof, term1: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      (s1.root.antecedent.filter(x => x.formula == term1)).toList match {
        case (x::_) => apply(s1, x)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, term1oc: Occurrence) = {
      val term1op = s1.antecedent.find(_ == term1oc)
      if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        term1
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
      val form = Neg(holterm1)
      term1.factory.createFormulaOccurrence(form, term1::Nil)
    }
    private def getSequent(s1: Sequent, term1: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val antecedent = createContext(s1.antecedent.filterNot(_ == term1))
      val succedent = createContext(s1.succedent) :+ prinFormula
      Sequent(antecedent, succedent)
    }
    def unapply(proof: LKProof) = if (proof.rule == NegRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }
}
