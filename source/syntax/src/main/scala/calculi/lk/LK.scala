/*
 * LK.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import at.logic.calculi.ExpressionOccurrences._
import at.logic.language.hol.HigherOrderLogic._
import at.logic.language.lambda.TypedLambdaCalculus._
import at.logic.utils.ds.Trees._
import scala.collection.immutable.{Set, EmptySet}

object LK {

    // List should be changed into multiset (I am not sure anymore as we need to map formula occurrences also in the original sequent.
    // For eaxmple when duplicating a branch we want to be able to know which formula is mapped to which)
    case class Sequent[A <: HOL](antecedent: List[Formula[A]], succedent: List[Formula[A]])
    // List should be changed into set
    case class SequentOccurrence[A <: HOL](antecedent: List[FormulaOccurrence[A]], succedent: List[FormulaOccurrence[A]])
    
    abstract class RuleTypeA
    abstract class NullaryRuleTypeA extends RuleTypeA
    abstract class UnaryRuleTypeA extends RuleTypeA
    abstract class BinaryRuleTypeA extends RuleTypeA

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

    // Quanitifier rules
    case object ForallLeftRuleType extends UnaryRuleTypeA
    case object ForallRightRuleType extends UnaryRuleTypeA
    case object ExistsLeftRuleType extends UnaryRuleTypeA
    case object ExistsRightRuleType extends UnaryRuleTypeA

    // exceptions
    class LKRuleException(msg: String) extends Exception(msg)
    class LKRuleCreationException(msg: String) extends LKRuleException(msg)
    class FormulaOutOfBoundException(msg: String) extends LKRuleException(msg)

    // lk proofs
    // rules are extracted in the form (UpperSequent(s), LowerSequent, AuxialiaryFormula(s), PrincipalFormula(s))
    trait LKProof[A <: HOL] extends Tree[SequentOccurrence[A]] {
        def root = vertex
        def rule: RuleTypeA
    }
    trait UnaryLKProof[A <: HOL] extends UnaryTree[SequentOccurrence[A]] with LKProof[A] {
        def uProof = t.asInstanceOf[LKProof[A]]
    }
    trait BinaryLKProof[A <: HOL] extends BinaryTree[SequentOccurrence[A]] with LKProof[A] {
        def uProof1 = t1.asInstanceOf[LKProof[A]]
        def uProof2 = t2.asInstanceOf[LKProof[A]]
    }
    
    // traits denoting having auxiliary and main formulas
    trait AuxiliaryFormulas[A <: HOL] {
        // for each upper sequent we have a list of occurrences
        def aux: List[List[FormulaOccurrence[A]]]
    }
    trait PrincipalFormulas[A <: HOL] {
        def prin: List[FormulaOccurrence[A]]
    }

    // running int for giving formula occurrences a specific id
    private var ids: Int = 0

    // convenient extractors
    object UnaryLKProof {
        def unapply[A <: HOL](proof: LKProof[A]) = proof match {
            case WeakeningLeftRule(up, r, p1) => Some((WeakeningLeftRuleType, up, r, Nil, p1))
            case WeakeningRightRule(up, r, p1) => Some((WeakeningRightRuleType, up, r, Nil, p1))
            case ContractionLeftRule(up, r, a1, a2, p1) => Some((ContractionLeftRuleType, up, r, a1::a2::Nil, p1))
            case ContractionRightRule(up, r, a1, a2, p1) => Some((ContractionRightRuleType, up, r, a1::a2::Nil, p1))
            case AndLeft1Rule(up, r, a, p) => Some((AndLeft1RuleType, up, r, a::Nil, p))
            case AndLeft2Rule(up, r, a, p) => Some((AndLeft2RuleType, up, r, a::Nil, p))
            case OrRight1Rule(up, r, a, p) => Some((OrRight1RuleType, up, r, a::Nil, p))
            case OrRight2Rule(up, r, a, p) => Some((OrRight2RuleType, up, r, a::Nil, p))
            case ImpRightRule(up, r, a1, a2, p) => Some((ImpRightRuleType, up, r, a1::a2::Nil, p))
            case NegLeftRule(up, r, a, p) => Some((NegLeftRuleType, up, r, a::Nil, p))
            case NegRightRule(up, r, a, p) => Some((NegRightRuleType, up, r, a::Nil, p))
            case _ => None
        }
    }

    object BinaryLKProof {
        def unapply[A <: HOL](proof: LKProof[A]) = proof match {
            case CutRule(up1, up2, r, a1, a2) => Some((CutRuleType, up1, up2, r, a1, a2, None))
            case AndRightRule(up1, up2, r, a1, a2, p) => Some((AndRightRuleType, up1, up2, r, a1, a2, Some(p)))
            case OrLeftRule(up1, up2, r, a1, a2, p) => Some((OrLeftRuleType, up1, up2, r, a1, a2, Some(p)))
            case ImpLeftRule(up1, up2, r, a1, a2, p) => Some((ImpLeftRuleType, up1, up2, r, a1, a2, Some(p)))
            case _ => None
        }
    }
    
    // actual rule extractor/factories
    object Axiom {  
        def apply[A <: HOL](seq: Sequent[A]) =
            new LeafTree[SequentOccurrence[A]](SequentOccurrence(seq.antecedent.map(createOccurrence[A]), seq.succedent.map(createOccurrence[A]))) with LKProof[A] {def rule = InitialRuleType}
        def createOccurrence[A <: HOL](f: Formula[A]): FormulaOccurrence[A] = { ids = ids + 1; FormulaOccurrence[A](f, BaseOccur(ids)) }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == InitialRuleType) Some((proof.root)) else None
    }

    object WeakeningLeftRule {
        def apply[A <: HOL](s1: LKProof[A], f: Formula[A]) = {
            ids = ids + 1
            val prinFormula = FormulaOccurrence[A](f, BaseOccur(ids))
            new UnaryTree[SequentOccurrence[A]](SequentOccurrence(prinFormula :: s1.root.antecedent, s1.root.succedent), s1)
                with UnaryLKProof[A] with PrincipalFormulas[A] {
                    def rule = WeakeningLeftRuleType
                    def prin = prinFormula::Nil
                }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == WeakeningLeftRuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with PrincipalFormulas[A]]
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, p1))
            }
            else None
    }

    object WeakeningRightRule {
        def apply[A <: HOL](s1: LKProof[A], f: Formula[A]) = {
            ids = ids + 1
            val prinFormula = FormulaOccurrence[A](f, BaseOccur(ids))
            new UnaryTree[SequentOccurrence[A]](SequentOccurrence(s1.root.antecedent, prinFormula :: s1.root.succedent), s1)
                with UnaryLKProof[A] with PrincipalFormulas[A] {
                    def rule = WeakeningRightRuleType
                    def prin = prinFormula::Nil
                }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == WeakeningRightRuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with PrincipalFormulas[A]]
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, p1))
            }
            else None
    }

    object ContractionLeftRule {
        def apply[A <: HOL](s1: LKProof[A], term1: FormulaOccurrence[A], term2: FormulaOccurrence[A]) = {
            if (term1.formula != term2.formula) throw new LKRuleCreationException("Formulas to be contracted are not identical")
            else if (term1.label == term2.label) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
            else if (!s1.root.antecedent.contains(term1) || !s1.root.antecedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                    new UnaryTree[SequentOccurrence[A]](SequentOccurrence(s1.root.antecedent - term2, s1.root.succedent), s1)
                        with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                            def rule = ContractionLeftRuleType
                            def aux = (term1::term2::Nil)::Nil
                            def prin = term1::Nil
                        }
                }
        }
        // convenient method to choose the first two formulas
        def apply[A <: HOL](s1: LKProof[A], term1: Formula[A]): UnaryTree[SequentOccurrence[A]] with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]  = {
            s1.root.antecedent.filter(x => x.formula == term1) match {
                case (x::y::_) => apply(s1, x, y)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == ContractionLeftRuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::a2::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, a2, p1))
            }
            else None
    }

    object ContractionRightRule {
        def apply[A <: HOL](s1: LKProof[A], term1: FormulaOccurrence[A], term2: FormulaOccurrence[A]) = {
            if (term1.formula != term2.formula) throw new LKRuleCreationException("Formulas to be contracted are not identical")
            else if (term1.label == term2.label) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
            else if (!s1.root.succedent.contains(term1) || !s1.root.succedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                    new UnaryTree[SequentOccurrence[A]](SequentOccurrence(s1.root.antecedent, s1.root.succedent - term2), s1)
                        with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                            def rule = ContractionRightRuleType
                            def aux = (term1::term2::Nil)::Nil
                            def prin = term1::Nil
                        }
                }
        }
        // convenient method to choose the first two formulas
        def apply[A <: HOL](s1: LKProof[A], term1: Formula[A]): UnaryTree[SequentOccurrence[A]] with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]  = {
            s1.root.succedent.filter(x => x.formula == term1) match {
                case (x::y::_) => apply(s1, x, y)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == ContractionRightRuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::a2::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, a2, p1))
            }
            else None
    }

    object CutRule {
        def apply[A <: HOL](s1: LKProof[A], s2: LKProof[A], term1: FormulaOccurrence[A], term2: FormulaOccurrence[A]) = {
            if (term1.formula != term2.formula) throw new LKRuleCreationException("Formulas to be cut are not identical")
            else if (!s1.root.succedent.contains(term1) || !s1.root.antecedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                new BinaryTree[SequentOccurrence[A]](SequentOccurrence(
                            s1.root.antecedent ++ (s2.root.antecedent - term2),
                            (s1.root.succedent - term1) ++ s1.root.succedent
                        ),
                        s1, s2)
                    with BinaryLKProof[A] with AuxiliaryFormulas[A] {
                        def rule = CutRuleType
                        def aux = (term1::Nil)::(term2::Nil)::Nil
                    }
                }
        }
        // convenient method to choose the first two formulas
        def apply[A <: HOL](s1: LKProof[A], s2: LKProof[A], term1: Formula[A]): BinaryTree[SequentOccurrence[A]] with BinaryLKProof[A] with AuxiliaryFormulas[A]  = {
            (s1.root.succedent.filter(x => x.formula == term1),s2.root.antecedent.filter(x => x.formula == term1)) match {
                case ((x::_),(y::_)) => apply(s1, s2, x, y)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == CutRuleType) {
                val r = proof.asInstanceOf[BinaryLKProof[A] with AuxiliaryFormulas[A]]
                val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
                Some((r.uProof1, r.uProof1, r.root, a1, a2))
            }
            else None
    }

    object AndRightRule {
        def apply[A <: HOL](s1: LKProof[A], s2: LKProof[A], term1: FormulaOccurrence[A], term2: FormulaOccurrence[A]) = {
            if (!s1.root.succedent.contains(term1) || !s2.root.succedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(And(term1.formula, term2.formula), term1.merge(term2))
                new BinaryTree[SequentOccurrence[A]](SequentOccurrence(
                            s1.root.antecedent ++ s2.root.antecedent,
                            prinFormula :: ((s1.root.succedent - term1) ++ (s2.root.succedent - term2))
                        ),
                        s1, s2)
                    with BinaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = AndRightRuleType
                        def aux = ((term1)::Nil)::(term2::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first two formulas
        def apply[A <: HOL](s1: LKProof[A], s2: LKProof[A], term1: Formula[A], term2: Formula[A]): BinaryLKProof[A] with BinaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]  = {
            (s1.root.succedent.filter(x => x.formula == term1),s2.root.succedent.filter(x => x.formula == term2)) match {
                case ((x::_),(y::_)) => apply(s1, s2, x, y)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == AndRightRuleType) {
                val r = proof.asInstanceOf[BinaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof1, r.uProof2, r.root, a1, a2, p1))
            }
            else None
    }

    object AndLeft1Rule {
        def apply[A <: HOL](s1: LKProof[A], term1: FormulaOccurrence[A], term2: Formula[A]) = {
            if (!s1.root.antecedent.contains(term1)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(And(term1.formula, term2), term1.label)
                new UnaryTree[SequentOccurrence[A]](SequentOccurrence(prinFormula :: (s1.root.antecedent - term1), s1.root.succedent), s1)
                    with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = AndLeft1RuleType
                        def aux = ((term1)::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first  formula
        def apply[A <: HOL](s1: LKProof[A], term1: Formula[A], term2: Formula[A]): UnaryTree[SequentOccurrence[A]] with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] = {
            s1.root.antecedent.filter(x => x.formula == term1) match {
                case (x::_) => apply(s1, x, term2)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == AndLeft1RuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, p1))
            }
            else None
    }

    object AndLeft2Rule {
        def apply[A <: HOL](s1: LKProof[A], term1: Formula[A], term2: FormulaOccurrence[A]) = {
            if (!s1.root.antecedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(And(term1, term2.formula), term2.label)
                new UnaryTree[SequentOccurrence[A]](SequentOccurrence(prinFormula :: (s1.root.antecedent - term2), s1.root.succedent), s1)
                    with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = AndLeft2RuleType
                        def aux = ((term2)::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first  formula
        def apply[A <: HOL](s1: LKProof[A], term1: Formula[A], term2: Formula[A]): UnaryTree[SequentOccurrence[A]] with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] = {
            s1.root.antecedent.filter(x => x.formula == term2) match {
                case (x::_) => apply(s1, term1, x)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == AndLeft2RuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, p1))
            }
            else None
    }

    object OrLeftRule {
        def apply[A <: HOL](s1: LKProof[A], s2: LKProof[A], term1: FormulaOccurrence[A], term2: FormulaOccurrence[A]) = {
            if (!s1.root.antecedent.contains(term1) || !s2.root.antecedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Or(term1.formula, term2.formula), term1.merge(term2))
                new BinaryTree[SequentOccurrence[A]](SequentOccurrence(
                            prinFormula :: ((s1.root.antecedent - term1) ++ (s2.root.antecedent - term2)),
                            s1.root.succedent ++ s2.root.succedent
                        ),
                        s1, s2)
                    with BinaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = OrLeftRuleType
                        def aux = ((term1)::Nil)::(term2::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first two formulas
        def apply[A <: HOL](s1: LKProof[A], s2: LKProof[A], term1: Formula[A], term2: Formula[A]): BinaryTree[SequentOccurrence[A]] with BinaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]  = {
            (s1.root.antecedent.filter(x => x.formula == term1),s2.root.antecedent.filter(x => x.formula == term2)) match {
                case ((x::_),(y::_)) => apply(s1, s2, x, y)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == OrLeftRuleType) {
                val r = proof.asInstanceOf[BinaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof1, r.uProof2, r.root, a1, a2, p1))
            }
            else None
    }

    object OrRight1Rule {
        def apply[A <: HOL](s1: LKProof[A], term1: FormulaOccurrence[A], term2: Formula[A]) = {
            if (!s1.root.succedent.contains(term1)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Or(term1.formula, term2), term1.label)
                new UnaryTree[SequentOccurrence[A]](SequentOccurrence(s1.root.antecedent, prinFormula :: (s1.root.succedent - term1)), s1)
                    with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = OrRight1RuleType
                        def aux = ((term1)::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first  formula
        def apply[A <: HOL](s1: LKProof[A], term1: Formula[A], term2: Formula[A]): UnaryTree[SequentOccurrence[A]] with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] = {
            s1.root.succedent.filter(x => x.formula == term1) match {
                case (x::_) => apply(s1, x, term2)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == OrRight1RuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, p1))
            }
            else None
    }

    object OrRight2Rule {
        def apply[A <: HOL](s1: LKProof[A], term1: Formula[A], term2: FormulaOccurrence[A]) = {
            if (!s1.root.succedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Or(term1, term2.formula), term2.label)
                new UnaryTree[SequentOccurrence[A]](SequentOccurrence(s1.root.antecedent, prinFormula :: (s1.root.succedent - term2)), s1)
                    with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = OrRight2RuleType
                        def aux = ((term2)::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first  formula
        def apply[A <: HOL](s1: LKProof[A], term1: Formula[A], term2: Formula[A]): UnaryTree[SequentOccurrence[A]] with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] = {
            s1.root.succedent.filter(x => x.formula == term2) match {
                case (x::_) => apply(s1, term1, x)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == OrRight1RuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, p1))
            }
            else None
    }

    object ImpLeftRule {
        def apply[A <: HOL](s1: LKProof[A], s2: LKProof[A], term1: FormulaOccurrence[A], term2: FormulaOccurrence[A]) = {
            if (!s1.root.succedent.contains(term1) || !s2.root.antecedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Imp(term1.formula, term2.formula), term1.merge(term2))
                new BinaryTree[SequentOccurrence[A]](SequentOccurrence(
                            prinFormula :: (s1.root.antecedent  ++ (s2.root.antecedent - term2)),
                            (s1.root.succedent - term1) ++ s2.root.succedent
                        ),
                        s1, s2)
                    with BinaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = ImpLeftRuleType
                        def aux = (term1::Nil)::(term2::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == ImpLeftRuleType) {
                val r = proof.asInstanceOf[BinaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof1, r.uProof2, r.root, a1, a2, p1))
            }
            else None
    }

    object ImpRightRule {
        def apply[A <: HOL](s1: LKProof[A], term1: FormulaOccurrence[A], term2: FormulaOccurrence[A]) = {
            if (!s1.root.antecedent.contains(term1) || !s1.root.succedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Imp(term1.formula, term2.formula), term1.merge(term2))
                new UnaryTree[SequentOccurrence[A]](SequentOccurrence(s1.root.antecedent - term1, prinFormula :: (s1.root.succedent - term1)), s1)
                    with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = ImpRightRuleType
                        def aux = (term1::term2::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == ImpRightRuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::a2::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, a2, p1))
            }
            else None
    }

    object NegLeftRule {
        def apply[A <: HOL](s1: LKProof[A], term1: FormulaOccurrence[A]) = {
            if (!s1.root.succedent.contains(term1)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Neg(term1.formula), term1.label)
                new UnaryTree[SequentOccurrence[A]](SequentOccurrence(prinFormula :: s1.root.antecedent, s1.root.succedent - term1), s1)
                    with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = NegLeftRuleType
                        def aux = (term1::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == NegLeftRuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, p1))
            }
            else None
    }

    object NegRightRule {
        def apply[A <: HOL](s1: LKProof[A], term1: FormulaOccurrence[A]) = {
            if (!s1.root.antecedent.contains(term1)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Neg(term1.formula), term1.label)
                new UnaryTree[SequentOccurrence[A]](SequentOccurrence(s1.root.antecedent - term1, prinFormula :: s1.root.succedent), s1)
                    with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = NegRightRuleType
                        def aux = (term1::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == NegRightRuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, p1))
            }
            else None
    }
/*
    object ForallLeftRule {
        def apply[A <: HOL](s1: LKProof[A], f: FormulaOccurrence[A], pos: Position) = {
            if (!s1.root.antecedent.contains(f)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Neg(term1.formula), term1.label)
                new UnaryTree[SequentOccurrence[A]](SequentOccurrence(s1.root.antecedent - term1, prinFormula :: s1.root.succedent), s1)
                    with UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A] {
                        def rule = NegRightRuleType
                        def aux = (term1::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == NegRightRuleType) {
                val r = proof.asInstanceOf[UnaryLKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val ((a1::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, p1))
            }
            else None
    }
*/
}
