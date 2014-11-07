/*
 * definitionRules.scala
 *
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.utils.ds.trees._
import base._

// Definition rules
case object DefinitionLeftRuleType extends UnaryRuleTypeA
case object DefinitionRightRuleType extends UnaryRuleTypeA


object DefinitionLeftRule {

  /** <pre>Constructs a proof ending with a DefinitionLeft rule.
    * In it, a term A (marked by term1oc) is replaced by formula main,
    * i.e. A is defined as main.
    *
    * This rule does not check for contradictory definitions elsewhere in s1, and thus
    * the burden of correct usage is on the programmer!
    * Being a nonstandard rule, this is also incompatible with methods like extractExpansionTrees.
    * 
    * The rule: 
    *   (rest of s1)
    *   sL, A |- sR
    * --------------- (DefinitionLeft)
    * sL, main |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, A |- sR) as the bottommost sequent.
    * @param term1oc The occurrence of A in s1.
    * @param main The formula with which A is to be replaced.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence, main: HOLFormula) = {
    val aux_fo = getTerms(s1.root, term1oc)
    val prinFormula = aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)

    val ant = createContext(s1.root.antecedent.filterNot(_ == aux_fo))
    val antecedent = ant :+ prinFormula
    val succedent = createContext((s1.root.succedent))

    new UnaryTree[Sequent](Sequent(antecedent, succedent), s1 )
    with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = DefinitionLeftRuleType
      def aux = (aux_fo::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "d:l"
    }
  }

  /** <pre>Replaces a term by its definition.
    * In the returned sequent, a term A (marked by term1oc) is replaced by formula main,
    * i.e. A is defined as main.
    *
    * This rule does not check for contradictory definitions elsewhere in s1, and thus
    * the burden of correct usage is on the programmer!
    * Being a nonstandard rule, this is also incompatible with methods like extractExpansionTrees.
    * 
    * The rule: 
    *   (rest of s1)
    *   sL, A |- sR
    * --------------- (DefinitionLeft)
    * sL, main |- sR
    * </pre>
    * 
    * @param s1 Sequent (sL, A |- sR).
    * @param term1oc The occurrence of A in s1.
    * @param main The formula with which A is to be replaced.
    * @return The sequent (sL, main |- sR).
    */ 
  def apply(s1: Sequent, term1oc: FormulaOccurrence, main: HOLFormula) = {
    val aux_fo = getTerms(s1, term1oc)
    val prinFormula = aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
    
    val ant = createContext(s1.antecedent.filterNot(_ == aux_fo))
    val antecedent = ant :+ prinFormula
    val succedent = createContext((s1.succedent))
    
    Sequent(antecedent, succedent)
  }
  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence) = {
    val term1op = s1.antecedent.find(_ == term1oc)
    if (term1op == None) throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
    else {
      val aux_fo = term1op.get
      aux_fo
    }
  }

  /** <pre>Constructs a proof ending with a DefinitionLeft rule.
    * In it, a term aux is replaced by formula main,
    * i.e. aux is defined as main.
    *
    * This rule does not check for contradictory definitions elsewhere in s1, and thus
    * the burden of correct usage is on the programmer!
    * Being a nonstandard rule, this is also incompatible with methods like extractExpansionTrees.
    * 
    * The rule: 
    *  (rest of s1)
    *  sL, aux |- sR
    * ---------------- (DefinitionLeft)
    * sL, main |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, A |- sR) as the bottommost sequent.
    * @param aux The term to be replaced by its definition.
    * @param main The formula with which aux is to be replaced.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas =
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


object DefinitionRightRule {

  /** <pre>Constructs a proof ending with a DefinitionRight rule.
    * In it, a term A (marked by term1oc) is replaced by formula main,
    * i.e. A is defined as main.
    *
    * This rule does not check for contradictory definitions elsewhere in s1, and thus
    * the burden of correct usage is on the programmer!
    * Being a nonstandard rule, this is also incompatible with methods like extractExpansionTrees.
    * 
    * The rule: 
    *   (rest of s1)
    *   sL |- sR, A
    * --------------- (DefinitionRight)
    * sL |- sR, main
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, A) as the bottommost sequent.
    * @param term1oc The occurrence of A in s1.
    * @param main The formula with which A is to be replaced.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence, main: HOLFormula) = {
    val aux_fo = getTerms(s1.root, term1oc)
    val prinFormula = aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
    
    val antecedent = createContext(s1.root.antecedent)
    val suc = createContext(s1.root.succedent.filterNot(_ == aux_fo))
    val succedent = suc :+ prinFormula

    new UnaryTree[Sequent](Sequent(antecedent, succedent), s1 )
    with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = DefinitionRightRuleType
      def aux = (aux_fo::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "d:r"
    }
  }

  /** <pre>Replaces a term by its definition.
    * In the returned sequent, a term A (marked by term1oc) is replaced by formula main,
    * i.e. A is defined as main.
    *
    * This rule does not check for contradictory definitions elsewhere in s1, and thus
    * the burden of correct usage is on the programmer!
    * Being a nonstandard rule, this is also incompatible with methods like extractExpansionTrees.
    * 
    * The rule: 
    *   (rest of s1)
    *   sL |- sR, A
    * --------------- (DefinitionRight)
    * sL, main |- sR
    * </pre>
    * 
    * @param s1 Sequent (sL |- sR, A).
    * @param term1oc The occurrence of A in s1.
    * @param main The formula with which A is to be replaced.
    * @return The sequent (sL |- sR, main).
    */ 
  def apply(s1: Sequent, term1oc: FormulaOccurrence, main: HOLFormula) = {
     val aux_fo = getTerms(s1, term1oc)
    val prinFormula = aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
    
    val antecedent = createContext(s1.antecedent)
    val suc = createContext(s1.succedent.filterNot(_ == aux_fo))
    val succedent = suc :+ prinFormula

    Sequent(antecedent, succedent)
  }
  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence) = {
    val term1op = s1.succedent.find(_ == term1oc)
    if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val aux_fo = term1op.get
      aux_fo
    }
  }

  /** <pre>Constructs a proof ending with a DefinitionRight rule.
    * In it, a term aux is replaced by formula main,
    * i.e. aux is defined as main.
    *
    * This rule does not check for contradictory definitions elsewhere in s1, and thus
    * the burden of correct usage is on the programmer!
    * Being a nonstandard rule, this is also incompatible with methods like extractExpansionTrees.
    * 
    * The rule: 
    *  (rest of s1)
    *  sL |- sR, aux
    * ---------------- (DefinitionRight)
    * sL |- sR, main
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, A) as the bottommost sequent.
    * @param aux The term to be replaced by its definition.
    * @param main The formula with which aux is to be replaced.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas =
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
