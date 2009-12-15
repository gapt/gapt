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
import at.logic.calculi.lk.propositionalRules.{InitialRuleType, WeakeningLeftRuleType, WeakeningRightRuleType}
import at.logic.calculi.lk.propositionalRules.{Axiom => LKAxiom}
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.base.{LKProof,SequentOccurrence,createContext,UnaryLKProof,LKRuleCreationException}
import at.logic.calculi.occurrences._
import at.logic.language.hol.quantifiers._
import at.logic.language.hol.propositions.TypeSynonyms._

// lksk proofs
// rules are extracted in the form (UpperSequent(s), LowerSequent, AuxialiaryFormula(s), PrincipalFormula(s))

// actual rule extractor/factories
// Axioms (and weakenings) always return a pair(Proof, mapping) which maps the indices of the list given into the new occurrences.
object Axiom {
  def apply(seq: Sequent, maps: Pair[List[Label], List[Label]]): Pair[LKProof, Pair[List[LabelledFormulaOccurrence],List[LabelledFormulaOccurrence]]] = {
    val left: List[LabelledFormulaOccurrence] =
      seq.antecedent.zip(maps._1).map( p => createOccurrence( p._1, p._2 ) )
    val right: List[LabelledFormulaOccurrence] = 
      seq.succedent.zip(maps._2).map( p => createOccurrence( p._1, p._2 ) )
    // I think we want LeafTree[LabelledSequentOccurrence] here, but it's incompatible with LKProof
    (new LeafTree[SequentOccurrence](new LabelledSequentOccurrence(LKAxiom.toSet(left), LKAxiom.toSet(right) ) ) with LKProof {def rule = InitialRuleType}, (left,right))
  }
  def createOccurrence(f: Formula, l: Label): LabelledFormulaOccurrence = 
    LKskFOFactory.createInitialOccurrence(f, l)
  def unapply(proof: LKProof) = if (proof.rule == InitialRuleType) Some((proof.root)) else None
}

object WeakeningLeftRule {
  def apply(s1: LKProof, f: Formula, l: Label) = {
    val prinFormula = LKskFOFactory.createInitialOccurrence(f, l)
    // I think we want LeafTree[LabelledSequentOccurrence] here, but it's incompatible with LKProof
    new UnaryTree[SequentOccurrence](
      new LabelledSequentOccurrence(createContext(s1.root.antecedent).asInstanceOf[Set[LabelledFormulaOccurrence]] + prinFormula, createContext(s1.root.succedent).asInstanceOf[Set[LabelledFormulaOccurrence]]), s1)
      with UnaryLKProof with PrincipalFormulas {
        def rule = WeakeningLeftRuleType
        def prin = prinFormula::Nil
      }
  }
  def unapply(proof: LKProof) = if (proof.rule == WeakeningLeftRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with PrincipalFormulas]
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, p1))
    }
    else None
}

object WeakeningRightRule {
  def apply(s1: LKProof, f: Formula, l: Label) = {
    val prinFormula = LKskFOFactory.createInitialOccurrence(f, l)
    new UnaryTree[SequentOccurrence](
      new LabelledSequentOccurrence(createContext(s1.root.antecedent).asInstanceOf[Set[LabelledFormulaOccurrence]], createContext(s1.root.succedent).asInstanceOf[Set[LabelledFormulaOccurrence]] + prinFormula), s1)
      with UnaryLKProof with PrincipalFormulas {
        def rule = WeakeningRightRuleType
        def prin = prinFormula::Nil
      }
  }
  def unapply(proof: LKProof) = if (proof.rule == WeakeningRightRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with PrincipalFormulas]
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, p1))
    }
    else None
}

// Quanitifier rules
case object ForallSkLeftRuleType extends UnaryRuleTypeA
case object ForallSkRightRuleType extends UnaryRuleTypeA
case object ExistsSkLeftRuleType extends UnaryRuleTypeA
case object ExistsSkRightRuleType extends UnaryRuleTypeA

// def createWeakQuantMain(formula: Formula, ancestor: LabelledFormulaOccurrence, term: Option[LambdaExpression])

object ForallSkLeftRule {
  // removeFromLabel indicates whether to remove the term subst from the label of the main formula.
  def apply(s1: LKProof, auxf: LabelledFormulaOccurrence, main: Formula, subst: HOLTerm, removeFromLabel: Boolean) = {
    main match {
      case All( sub ) => {
        // TODO: comment in to check validity of the rule.
        // commented out at the moment because we don't know the subst term
        // in the XML parser. We need first-order unification for that.
        //assert( betaNormalize( App( sub, subst ) ) == aux )
        if ( !s1.root.antecedent.contains( auxf ) )
          throw new LKRuleCreationException("Premise does not contain the given formula occurrence.")
        if ( !auxf.label.contains( subst ) )
          throw new LKRuleCreationException("Auxiliary formula occurrence label of ForallSkLeftRule does not contain substitution term.")
        val prinFormula = 
          LKskFOFactory.createWeakQuantMain(main, auxf, if (removeFromLabel) Some(subst) else None)
        new UnaryTree[SequentOccurrence](
          new LabelledSequentOccurrence(createContext((s1.root.antecedent - auxf)).asInstanceOf[Set[LabelledFormulaOccurrence]] + prinFormula, createContext((s1.root.succedent)).asInstanceOf[Set[LabelledFormulaOccurrence]]), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
            def rule = ForallSkLeftRuleType
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
      case _ => throw new LKRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.")
    }
  }

  def unapply(proof: LKProof) = if (proof.rule == ForallSkLeftRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object ExistsSkRightRule {
  def apply(s1: LKProof, auxf: LabelledFormulaOccurrence, main: Formula, subst: HOLTerm, removeFromLabel: Boolean) = {
    main match {
      case Ex( sub ) => {
        //assert( betaNormalize( App( sub, subst ) ) == aux )
        if ( !s1.root.succedent.contains( auxf ) )
          throw new LKRuleCreationException("Premise does not contain the given formula occurrence.")
        if ( !auxf.label.contains( subst ) )
          throw new LKRuleCreationException("Auxiliary formula occurrence label of ForallSkLeftRule does not contain substitution term.")
        val prinFormula = 
          LKskFOFactory.createWeakQuantMain(main, auxf, if (removeFromLabel) Some(subst) else None)
        new UnaryTree[SequentOccurrence](
          new LabelledSequentOccurrence(createContext(s1.root.antecedent).asInstanceOf[Set[LabelledFormulaOccurrence]], createContext((s1.root.succedent - auxf)).asInstanceOf[Set[LabelledFormulaOccurrence]] + prinFormula), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
            def rule = ExistsSkRightRuleType
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
      case _ => throw new LKRuleCreationException("Main formula of ExistsSkRightRule must have a universal quantifier as head symbol.")
    }
  }

  def unapply(proof: LKProof) = if (proof.rule == ExistsSkRightRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object ForallSkRightRule {
  def apply(s1: LKProof, auxf: LabelledFormulaOccurrence, main: Formula, skolem_term: HOLTerm) = {
    main match {
      case All( sub ) => {
        // TODO: check Skolem term
        if (!s1.root.succedent.contains( auxf ) )
          throw new LKRuleCreationException("Premise does not contain the given formula occurrence.")
        val prinFormula = auxf.factory.createPrincipalFormulaOccurrence(main, auxf::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryTree[SequentOccurrence](
          new LabelledSequentOccurrence(createContext(s1.root.antecedent).asInstanceOf[Set[LabelledFormulaOccurrence]], createContext((s1.root.succedent - auxf)).asInstanceOf[Set[LabelledFormulaOccurrence]] + prinFormula), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
            def rule = ForallSkRightRuleType
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
          }
        }
      case _ => throw new LKRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.")
    }
  }

  def unapply(proof: LKProof) = if (proof.rule == ForallSkRightRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object ExistsSkLeftRule {
  def apply(s1: LKProof, auxf: LabelledFormulaOccurrence, main: Formula, skolem_term: HOLTerm) = {
    main match {
      case Ex( sub ) => {
        // TODO: check Skolem term
        if (!s1.root.antecedent.contains( auxf ) )
          throw new LKRuleCreationException("Premise does not contain the given formula occurrence.")
        val prinFormula = auxf.factory.createPrincipalFormulaOccurrence(main, auxf::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryTree[SequentOccurrence](
          new LabelledSequentOccurrence(createContext((s1.root.antecedent - auxf)).asInstanceOf[Set[LabelledFormulaOccurrence]] + prinFormula, createContext((s1.root.succedent)).asInstanceOf[Set[LabelledFormulaOccurrence]]), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
            def rule = ExistsSkLeftRuleType
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
          }
        }
      case _ => throw new LKRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.")
    }
  }

  def unapply(proof: LKProof) = if (proof.rule == ExistsSkLeftRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}
