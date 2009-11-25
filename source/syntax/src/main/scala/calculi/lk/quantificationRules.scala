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
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.propositions._
import at.logic.language.hol.quantifiers._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap
import base._

package quantificationRules {

  // Quanitifier rules
  case object ForallLeftRuleType extends UnaryRuleTypeA
  case object ForallRightRuleType extends UnaryRuleTypeA
  case object ExistsLeftRuleType extends UnaryRuleTypeA
  case object ExistsRightRuleType extends UnaryRuleTypeA

  object ForallLeftRule {
    def apply(s1: LKProof, aux: Formula, main: Formula, subst: HOLTerm) = {
      main match {
        case All( sub ) => {
          // TODO: comment in to check validity of the rule.
          // commented out at the moment because we don't know the subst term
          // in the XML parser. We need first-order unification for that.
          //assert( betaNormalize( App( sub, subst ) ) == aux )
          s1.root.antecedent.filter( x => x.formula == aux ).toList match {
            case (x::_) => {
              val prinFormula = FormulaOccurrence( main, x )
              new UnaryTree[SequentOccurrence](
                  SequentOccurrence(createContext((s1.root.antecedent - x)) + prinFormula,
                                    createContext((s1.root.succedent))), s1 )
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                def rule = ForallLeftRuleType
                def aux = (x::Nil)::Nil
                def prin = prinFormula::Nil
              }
            }
            case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
            }
        }
        case _ => throw new LKRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.")
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == ForallLeftRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }

  object ExistsRightRule {
    def apply(s1: LKProof, aux: Formula, main: Formula, subst: HOLTerm) = {
      main match {
        case Ex( sub ) => {
          //assert( betaNormalize( App( sub, subst ) ) == aux )
          s1.root.succedent.filter( x => x.formula == aux ).toList match {
            case (x::_) => {
              val prinFormula = FormulaOccurrence( main, x )
              new UnaryTree[SequentOccurrence](
                  SequentOccurrence(createContext(s1.root.antecedent),
                                    createContext((s1.root.succedent - x)) + prinFormula), s1 )
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                def rule = ExistsRightRuleType
                def aux = (x::Nil)::Nil
                def prin = prinFormula::Nil
              }
            }
            case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
            }
        }
        case _ => throw new LKRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.")
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == ExistsRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }

  object ForallRightRule {
    def apply(s1: LKProof, aux: Formula, main: Formula, eigenvar: HOLVar) = {
      main match {
        case All( sub ) => {
          // TODO: check eigenvariable condition
          //assert( betaNormalize( App( sub, eigenvar ) ) == aux )
          s1.root.succedent.filter( x => x.formula == aux ).toList match {
            case (x::_) => {
              val prinFormula = FormulaOccurrence( main, x )
              new UnaryTree[SequentOccurrence](
                  SequentOccurrence(createContext(s1.root.antecedent),
                                    createContext((s1.root.succedent - x)) + prinFormula), s1 )
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                def rule = ForallRightRuleType
                def aux = (x::Nil)::Nil
                def prin = prinFormula::Nil
              }
            }
            case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
            }
        }
        case _ => throw new LKRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.")
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == ForallRightRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }

  object ExistsLeftRule {
    def apply(s1: LKProof, aux: Formula, main: Formula, eigenvar: HOLVar) = {
      main match {
        case Ex( sub ) => {
          // TODO: check eigenvariable condition
          //assert( betaNormalize( App( sub, eigenvar ) ) == aux )
          s1.root.antecedent.filter( x => x.formula == aux ).toList match {
            case (x::_) => {
              val prinFormula = FormulaOccurrence( main, x )
              new UnaryTree[SequentOccurrence](
                  SequentOccurrence(createContext((s1.root.antecedent - x)) + prinFormula,
                                    createContext((s1.root.succedent))), s1 )
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                def rule = ExistsLeftRuleType
                def aux = (x::Nil)::Nil
                def prin = prinFormula::Nil
              }
            }
            case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
            }
        }
        case _ => throw new LKRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.")
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == ExistsLeftRuleType) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }
}
