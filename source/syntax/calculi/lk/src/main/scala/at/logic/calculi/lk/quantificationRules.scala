/*
 * quantificationRules.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import propositionalRules._
import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap
import base._

package quantificationRules {

import _root_.at.logic.utils.traits.Occurrence

// Quanitifier rules
  case object ForallLeftRuleType extends UnaryRuleTypeA
  case object ForallRightRuleType extends UnaryRuleTypeA
  case object ExistsLeftRuleType extends UnaryRuleTypeA
  case object ExistsRightRuleType extends UnaryRuleTypeA

  object ForallLeftRule {
    def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula, term: HOLExpression) : LKProof = {
      s1.root.antecedent.filter( x => x.formula == aux ).toList match {
        case (x::_) => apply( s1, x, main, term )
        case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula.")
      }
    }

    def computeAux( main: HOLFormula, term: HOLExpression ) = main match {
      // TODO: make betaNormalize that respects closure of HOLFormula under normalization
      case All( sub, _ ) => betaNormalize( App( sub, term ) ).asInstanceOf[HOLFormula]
      case _ => throw new LKRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.")
    }

    def apply(s1: LKProof, term1oc: Occurrence, main: HOLFormula, term: HOLExpression) : LKProof = {
      val (aux_fo, aux_form) = getTerms(s1.root, term1oc, main, term)
      val prinFormula = getPrinFormula(main, aux_fo)
      val sequent = getSequent(s1.root, aux_fo, prinFormula)

      new UnaryTree[Sequent](sequent, s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
        def rule = ForallLeftRuleType
        def aux = (aux_fo::Nil)::Nil
        def prin = prinFormula::Nil
        def subst = term
        override def name = "\u2200:l"
      }
    }
    def apply(s1: Sequent, term1oc: Occurrence, main: HOLFormula, term: HOLExpression) = {
      val (aux_fo, aux_form) = getTerms(s1, term1oc, main, term)
      val prinFormula = getPrinFormula(main, aux_fo)
      getSequent(s1, aux_fo, prinFormula)
    }
    private def getTerms(s1: Sequent, term1oc: Occurrence, main: HOLFormula, term: HOLExpression) = {
      val term1op = s1.antecedent.find(_ == term1oc)
      if (term1op == None) {
        println("=====================")
        def o2s(occ:FormulaOccurrence) = occ +" formula="+occ.formula+ " ancestors="+occ.ancestors
        println(o2s(term1oc.asInstanceOf[FormulaOccurrence]))
        //s1.antecedent.head.ancestors foreach ( (x:FormulaOccurrence) => println(o2s(x)))
        println(o2s(s1.antecedent.head))
        println(main)
        println(term)
        throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      }
      else {
        val aux_fo = term1op.get
        val aux_form = computeAux(main, term)
        assert( aux_form == aux_fo.formula, "The computed auxiliary formula " + aux_form.toString + " is not equal to the formula " + aux_fo.formula.toString + " at the given occurrence ("+aux_form.toPrettyString + " != " + aux_fo.formula.toPrettyString+")")
        (aux_fo, aux_form)
      }
    }
    private def getPrinFormula(main: HOLFormula, aux_fo: FormulaOccurrence) = {
      aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
    }
    private def getSequent(s1: Sequent, aux_fo: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val ant = createContext(s1.antecedent.filterNot(_ == aux_fo))
      val antecedent = ant :+ prinFormula
      val succedent = createContext(s1.succedent)
      Sequent(antecedent, succedent)
    } 
    def unapply(proof: LKProof) = if (proof.rule == ForallLeftRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1, r.subst))
      }
      else None
  }

  object ExistsRightRule {
    def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula, term: HOLExpression) : LKProof = {
      s1.root.succedent.filter( x => x.formula == aux ).toList match {
        case (x::_) => apply( s1, x, main, term )
        case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
        }
    }

    def computeAux( main: HOLFormula, term: HOLExpression ) = main match {
      // TODO: make betaNormalize that respects closure of HOLFormula under normalization
      case Ex( sub, _ ) => betaNormalize( App( sub, term ) ).asInstanceOf[HOLFormula]
      case _ => throw new LKRuleCreationException("Main formula of ExistsRightRule must have a universal quantifier as head symbol.")
    }

    def apply(s1: LKProof, term1oc: Occurrence, main: HOLFormula, term: HOLExpression) : LKProof = {
      val aux_fo = getTerms(s1.root, term1oc, main, term)
      val prinFormula = getPrinFormula(main, aux_fo) 
      val sequent = getSequent(s1.root, aux_fo, prinFormula)

      new UnaryTree[Sequent](sequent, s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
        def rule = ExistsRightRuleType
        def aux = (aux_fo::Nil)::Nil
        def prin = prinFormula::Nil
        def subst = term
        override def name = "\u2203:r"
      }
    }
    def apply(s1: Sequent, term1oc: Occurrence, main: HOLFormula, term: HOLExpression) = {
      val aux_fo = getTerms(s1, term1oc, main, term)
      val prinFormula = getPrinFormula(main, aux_fo) 
      getSequent(s1, aux_fo, prinFormula)
    }
    private def getTerms(s1: Sequent, term1oc: Occurrence, main: HOLFormula, term: HOLExpression) = {
      val term1op = s1.succedent.find(_ == term1oc)
      if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val aux_fo = term1op.get
        assert( computeAux( main, term ) == aux_fo.formula, computeAux( main, term ).toStringSimple + " is not " + aux_fo.formula.toStringSimple )
        aux_fo
      }
    }
    private def getPrinFormula(main: HOLFormula, aux_fo: FormulaOccurrence) = {
      aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
    }
    private def getSequent(s1: Sequent, aux_fo: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val antecedent = createContext(s1.antecedent)
      val suc = createContext(s1.succedent.filterNot(_ == aux_fo))
      val succedent = suc :+ prinFormula
      Sequent(antecedent, succedent)
    } 
    def unapply(proof: LKProof) = if (proof.rule == ExistsRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1, r.subst))
      }
      else None
  }

  object ForallRightRule {
    def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula, eigen_var: HOLVar) : LKProof =
      s1.root.succedent.filter( x => x.formula == aux ).toList match {
        case (x::_) => apply( s1, x, main, eigen_var )
        case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
      }

    def apply( s1: LKProof, term1oc: Occurrence, main: HOLFormula, eigen_var: HOLVar ) : LKProof = {
      val aux_fo = getTerms(s1.root, term1oc, main, eigen_var)
      val prinFormula = getPrinFormula(main, aux_fo)
      val sequent = getSequent(s1.root, aux_fo, prinFormula)

      new UnaryTree[Sequent](sequent, s1 )
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable {
          def rule = ForallRightRuleType
          def aux = (aux_fo::Nil)::Nil
          def prin = prinFormula::Nil
          def eigenvar = eigen_var
          override def name = "\u2200:r"
        }
    }
    def apply( s1: Sequent, term1oc: Occurrence, main: HOLFormula, eigen_var: HOLVar ) = {
      val aux_fo = getTerms(s1, term1oc, main, eigen_var)
      val prinFormula = getPrinFormula(main, aux_fo)
      getSequent(s1, aux_fo, prinFormula)
    }
    private def getTerms(s1: Sequent, term1oc: Occurrence, main: HOLFormula, eigen_var: HOLVar) = {
      val term1op = s1.succedent.find(_ == term1oc)
      if (term1op == None) throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      else {
        val aux_fo = term1op.get
        main match {
          case All( sub, _ ) => {
            // eigenvar condition
            assert( ( s1.antecedent ++ (s1.succedent.filterNot(_ == aux_fo)) ).forall( fo => !fo.formula.getFreeAndBoundVariables._1.contains( eigen_var ) ),
              "Eigenvariable " + eigen_var.toStringSimple + " occurs in context " + s1.toStringSimple )
            // correct auxiliary formula
//            println("ForallRightRule")
//            println("eigen_var = "+eigen_var)
//            println("betaNormalize( App( sub, eigen_var ): " + betaNormalize( App( sub, eigen_var )))
//            println("aux_fo: " + aux_fo.formula)
            assert( betaNormalize( App( sub, eigen_var ) ) == aux_fo.formula )
            aux_fo 
          }
          case _ => throw new LKRuleCreationException("Main formula of ForallRightRule must have a universal quantifier as head symbol.")
        }
      }
    }
    private def getPrinFormula(main: HOLFormula, aux_fo: FormulaOccurrence) = {
      aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
    }
    private def getSequent(s1: Sequent, aux_fo: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val antecedent = createContext(s1.antecedent)
      val suc = createContext(s1.succedent.filterNot(_ == aux_fo))
      val succedent = suc :+ prinFormula
      Sequent(antecedent, succedent)
    } 
    def unapply(proof: LKProof) = if (proof.rule == ForallRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1, r.eigenvar))
      }
      else None
  }

  object ExistsLeftRule {
    def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula, eigen_var: HOLVar) : LKProof =
      s1.root.antecedent.filter( x => x.formula == aux ).toList match {
        case (x::_) => apply( s1, x, main, eigen_var )
        case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
      }

    def apply( s1: LKProof, term1oc: Occurrence, main: HOLFormula, eigen_var: HOLVar ) : LKProof = {
      val aux_fo = getTerms(s1.root, term1oc, main, eigen_var)
      val prinFormula = getPrinFormula(main, aux_fo)
      val sequent = getSequent(s1.root, aux_fo, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable {
        def rule = ExistsLeftRuleType
        def aux = (aux_fo::Nil)::Nil
        def prin = prinFormula::Nil
        def eigenvar = eigen_var
        override def name = "\u2203:l"
      }
    }
    def apply( s1: Sequent, term1oc: Occurrence, main: HOLFormula, eigen_var: HOLVar ) = {
      val aux_fo = getTerms(s1, term1oc, main, eigen_var)
      val prinFormula = getPrinFormula(main, aux_fo)
      getSequent(s1, aux_fo, prinFormula)
    }
    private def getTerms( s1: Sequent, term1oc: Occurrence, main: HOLFormula, eigen_var: HOLVar ) = {
      val term1op = s1.antecedent.find(_ == term1oc)
      if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val aux_fo = term1op.get
        main match {
          case Ex( sub, _ ) => {
            // eigenvar condition
            assert( ( (s1.antecedent.filterNot(_ == aux_fo)) ++ s1.succedent ).forall( fo => !fo.formula.getFreeAndBoundVariables._1.contains( eigen_var ) ),
              "Eigenvariable " + eigen_var.toStringSimple + " occurs in context " + s1.toStringSimple )
            // correct auxiliary formula
            assert( betaNormalize( App( sub, eigen_var ) ) == aux_fo.formula )
            aux_fo
          }
          case _ => throw new LKRuleCreationException("Main formula of ExistsLeftRule must have an existential quantifier as head symbol.")
        }
      }
    }
    private def getPrinFormula(main: HOLFormula, aux_fo: FormulaOccurrence) = {
      aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
    }
    private def getSequent(s1: Sequent, aux_fo: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
      val ant = createContext(s1.antecedent.filterNot(_ == aux_fo))
      val antecedent = ant :+ prinFormula
      val succedent = createContext((s1.succedent))
      Sequent(antecedent, succedent)
    } 
    def unapply(proof: LKProof) = if (proof.rule == ExistsLeftRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1, r.eigenvar))
    }
    else None
  }
}
