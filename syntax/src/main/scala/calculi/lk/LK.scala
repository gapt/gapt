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
import scala.collection.immutable.Set

object LK {

    // List should be changed into multiset (I am not sure anymore as we need to map formula occurrences also in the original sequent.
    // For eaxmple when duplicating a branch we want to be able to know which formula is mapped to which)
    case class Sequent(antecedent: List[Formula], succedent: List[Formula])
    // List should be changed into set
    case class SequentOccurrence(antecedent: Set[FormulaOccurrence], succedent: Set[FormulaOccurrence])
    
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
    class FormulaNotExistsException(msg: String) extends LKRuleException(msg)

    // lk proofs
    // rules are extracted in the form (UpperSequent(s), LowerSequent, AuxialiaryFormula(s), PrincipalFormula(s))
    trait LKProof extends Tree[SequentOccurrence] {
        def root = vertex
        def rule: RuleTypeA
        def getDescendantInLowerSequent(fo: FormulaOccurrence) = {
            val set = getOccurrence(fo.label, (root.antecedent ++ root.succedent).asInstanceOf[Set[Occurrence]]).asInstanceOf[Set[FormulaOccurrence]] // double casting because set is invariant in the type parameter
            set.toList match {
                case x::Nil if x.ancestors.contains(fo) => x
                case _ => throw new FormulaNotExistsException("Cannot find descendant formula")
            }
        }
        
    }
    trait UnaryLKProof extends UnaryTree[SequentOccurrence] with LKProof {
        def uProof = t.asInstanceOf[LKProof]

    }
    trait BinaryLKProof extends BinaryTree[SequentOccurrence] with LKProof {
        def uProof1 = t1.asInstanceOf[LKProof]
        def uProof2 = t2.asInstanceOf[LKProof]
    }
    
    // traits denoting having auxiliary and main formulas
    trait AuxiliaryFormulas {
        // for each upper sequent we have a list of occurrences
        def aux: List[List[FormulaOccurrence]]
    }
    trait PrincipalFormulas {
        def prin: List[FormulaOccurrence]
    }

    // convenient extractors
    object UnaryLKProof {
        def unapply(proof: LKProof) = proof match {
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
        def unapply(proof: LKProof) = proof match {
            case CutRule(up1, up2, r, a1, a2) => Some((CutRuleType, up1, up2, r, a1, a2, None))
            case AndRightRule(up1, up2, r, a1, a2, p) => Some((AndRightRuleType, up1, up2, r, a1, a2, Some(p)))
            case OrLeftRule(up1, up2, r, a1, a2, p) => Some((OrLeftRuleType, up1, up2, r, a1, a2, Some(p)))
            case ImpLeftRule(up1, up2, r, a1, a2, p) => Some((ImpLeftRuleType, up1, up2, r, a1, a2, Some(p)))
            case _ => None
        }
    }

    // should be optimized as it was done now just to save coding time
    def toSet[T](list: List[T]) = {
        def traverse(list: List[T])(set: Set[T]): Set[T] = list match {
            case hd :: tail => traverse(tail)(set + hd)   // create a new Set, adding hd
            case Nil => set
        }
        traverse(list)(Set[T]())
    }

    // actual rule extractor/factories
    // Axioms (and weakenings) always return a pair(Proof, mapping) which maps the indices of the list given into the new occurrences.
    // It is used together with an implicit conversion between this pair into a proof so users who are not interested in this information will not see it.
    object Axiom {  
        def apply(seq: Sequent): Pair[LKProof, Pair[List[FormulaOccurrence],List[FormulaOccurrence]]] = {
            val left: List[FormulaOccurrence] = seq.antecedent.map(createOccurrence)
            val right: List[FormulaOccurrence] = seq.succedent.map(createOccurrence)
            (new LeafTree[SequentOccurrence](SequentOccurrence(toSet(left), toSet(right))) with LKProof {def rule = InitialRuleType}, (left,right))
        }
            
        def createOccurrence(f: Formula): FormulaOccurrence = FormulaOccurrence(f)
        def unapply(proof: LKProof) = if (proof.rule == InitialRuleType) Some((proof.root)) else None
    }
    implicit def axiomMapToAxiom(axiomMap: Pair[LKProof, Pair[List[FormulaOccurrence],List[FormulaOccurrence]]]): LKProof = axiomMap._1

    // create new formula occurrences in the new context
    private def createContext(set: Set[FormulaOccurrence]): Set[FormulaOccurrence] = set.map(x => FormulaOccurrence(x.formula, x))

    object WeakeningLeftRule {
        def apply(s1: LKProof, f: Formula) = {
            val prinFormula = FormulaOccurrence(f)
            new UnaryTree[SequentOccurrence](SequentOccurrence(createContext(s1.root.antecedent) + prinFormula, createContext(s1.root.succedent)), s1)
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
        def apply(s1: LKProof, f: Formula) = {
            val prinFormula = FormulaOccurrence(f)
            new UnaryTree[SequentOccurrence](SequentOccurrence(createContext(s1.root.antecedent), createContext(s1.root.succedent) + prinFormula), s1)
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

    object ContractionLeftRule {
        def apply(s1: LKProof, term1: FormulaOccurrence, term2: FormulaOccurrence) = {
            if (term1.formula != term2.formula) throw new LKRuleCreationException("Formulas to be contracted are not identical")
            else if (term1.label == term2.label) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
            else if (!s1.root.antecedent.contains(term1) || !s1.root.antecedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(term1)
                new UnaryTree[SequentOccurrence](SequentOccurrence(createContext(s1.root.antecedent - term1 - term2) + prinFormula, createContext(s1.root.succedent)), s1)
                        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                            def rule = ContractionLeftRuleType
                            def aux = (term1::term2::Nil)::Nil
                            def prin = prinFormula::Nil
                        }
                }
        }
        // convenient method to choose the first two formulas
        def apply(s1: LKProof, term1: Formula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
            (s1.root.antecedent.filter(x => x.formula == term1)).toList match {
                case (x::y::_) => apply(s1, x, y)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
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
        def apply(s1: LKProof, term1: FormulaOccurrence, term2: FormulaOccurrence) = {
            if (term1.formula != term2.formula) throw new LKRuleCreationException("Formulas to be contracted are not identical")
            else if (term1.label == term2.label) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
            else if (!s1.root.succedent.contains(term1) || !s1.root.succedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(term1)
                    new UnaryTree[SequentOccurrence](SequentOccurrence(createContext(s1.root.antecedent), createContext(s1.root.succedent - term1 - term2) + prinFormula), s1)
                        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                            def rule = ContractionRightRuleType
                            def aux = (term1::term2::Nil)::Nil
                            def prin = term1::Nil
                        }
                }
        }
        // convenient method to choose the first two formulas
        def apply(s1: LKProof, term1: Formula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
            (s1.root.succedent.filter(x => x.formula == term1)).toList match {
                case (x::y::_) => apply(s1, x, y)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
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
        def apply(s1: LKProof, s2: LKProof, term1: FormulaOccurrence, term2: FormulaOccurrence) = {
            if (term1.formula != term2.formula) throw new LKRuleCreationException("Formulas to be cut are not identical")
            else if (!s1.root.succedent.contains(term1) || !s1.root.antecedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                new BinaryTree[SequentOccurrence](SequentOccurrence(
                            createContext(s1.root.antecedent ++ (s2.root.antecedent - term2)),
                            createContext((s1.root.succedent - term1) ++ s1.root.succedent)
                        ),
                        s1, s2)
                    with BinaryLKProof with AuxiliaryFormulas {
                        def rule = CutRuleType
                        def aux = (term1::Nil)::(term2::Nil)::Nil
                    }
                }
        }
        // convenient method to choose the first two formulas
        def apply(s1: LKProof, s2: LKProof, term1: Formula): BinaryTree[SequentOccurrence] with BinaryLKProof with AuxiliaryFormulas  = {
            ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term1)).toList) match {
                case ((x::_),(y::_)) => apply(s1, s2, x, y)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply(proof: LKProof) = if (proof.rule == CutRuleType) {
                val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas]
                val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
                Some((r.uProof1, r.uProof1, r.root, a1, a2))
            }
            else None
    }

    object AndRightRule {
        def apply(s1: LKProof, s2: LKProof, term1: FormulaOccurrence, term2: FormulaOccurrence) = {
            if (!s1.root.succedent.contains(term1) || !s2.root.succedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(And(term1.formula, term2.formula), term1, term2)
                new BinaryTree[SequentOccurrence](SequentOccurrence(
                            createContext(s1.root.antecedent ++ s2.root.antecedent),
                            createContext(((s1.root.succedent - term1) ++ (s2.root.succedent - term2))) + prinFormula
                        ),
                        s1, s2)
                    with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = AndRightRuleType
                        def aux = ((term1)::Nil)::(term2::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first two formulas
        def apply(s1: LKProof, s2: LKProof, term1: Formula, term2: Formula): BinaryLKProof with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
            ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.succedent.filter(x => x.formula == term2)).toList) match {
                case ((x::_),(y::_)) => apply(s1, s2, x, y)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
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
        def apply(s1: LKProof, term1: FormulaOccurrence, term2: Formula) = {
            if (!s1.root.antecedent.contains(term1)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(And(term1.formula, term2), term1)
                new UnaryTree[SequentOccurrence](SequentOccurrence(createContext((s1.root.antecedent - term1)) + prinFormula, createContext(s1.root.succedent)), s1)
                    with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = AndLeft1RuleType
                        def aux = ((term1)::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first  formula
        def apply(s1: LKProof, term1: Formula, term2: Formula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
            (s1.root.antecedent.filter(x => x.formula == term1)).toList match {
                case (x::_) => apply(s1, x, term2)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
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
        def apply(s1: LKProof, term1: Formula, term2: FormulaOccurrence) = {
            if (!s1.root.antecedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(And(term1, term2.formula), term2)
                new UnaryTree[SequentOccurrence](SequentOccurrence(createContext((s1.root.antecedent - term2)) + prinFormula, createContext(s1.root.succedent)), s1)
                    with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = AndLeft2RuleType
                        def aux = ((term2)::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first  formula
        def apply(s1: LKProof, term1: Formula, term2: Formula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
            (s1.root.antecedent.filter(x => x.formula == term2)).toList match {
                case (x::_) => apply(s1, term1, x)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
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
        def apply(s1: LKProof, s2: LKProof, term1: FormulaOccurrence, term2: FormulaOccurrence) = {
            if (!s1.root.antecedent.contains(term1) || !s2.root.antecedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Or(term1.formula, term2.formula), term1, term2)
                new BinaryTree[SequentOccurrence](SequentOccurrence(
                            ((createContext(s1.root.antecedent - term1) ++ (s2.root.antecedent - term2))) + prinFormula,
                            createContext(s1.root.succedent ++ s2.root.succedent)
                        ),
                        s1, s2)
                    with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = OrLeftRuleType
                        def aux = ((term1)::Nil)::(term2::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first two formulas
        def apply(s1: LKProof, s2: LKProof, term1: Formula, term2: Formula): BinaryTree[SequentOccurrence] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
            ((s1.root.antecedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term2)).toList) match {
                case ((x::_),(y::_)) => apply(s1, s2, x, y)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
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
        def apply(s1: LKProof, term1: FormulaOccurrence, term2: Formula) = {
            if (!s1.root.succedent.contains(term1)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Or(term1.formula, term2), term1)
                new UnaryTree[SequentOccurrence](SequentOccurrence(createContext(s1.root.antecedent), createContext((s1.root.succedent - term1)) + prinFormula), s1)
                    with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = OrRight1RuleType
                        def aux = ((term1)::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first  formula
        def apply(s1: LKProof, term1: Formula, term2: Formula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
            (s1.root.succedent.filter(x => x.formula == term1)).toList match {
                case (x::_) => apply(s1, x, term2)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
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
        def apply(s1: LKProof, term1: Formula, term2: FormulaOccurrence) = {
            if (!s1.root.succedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Or(term1, term2.formula), term2)
                new UnaryTree[SequentOccurrence](SequentOccurrence(createContext(s1.root.antecedent), createContext((s1.root.succedent - term2)) + prinFormula), s1)
                    with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = OrRight2RuleType
                        def aux = ((term2)::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        // convenient method to choose the first  formula
        def apply(s1: LKProof, term1: Formula, term2: Formula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
            (s1.root.succedent.filter(x => x.formula == term2)).toList match {
                case (x::_) => apply(s1, term1, x)
                case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
            }
        }
        def unapply(proof: LKProof) = if (proof.rule == OrRight1RuleType) {
                val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
                val ((a1::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, p1))
            }
            else None
    }

    object ImpLeftRule {
        def apply(s1: LKProof, s2: LKProof, term1: FormulaOccurrence, term2: FormulaOccurrence) = {
            if (!s1.root.succedent.contains(term1) || !s2.root.antecedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Imp(term1.formula, term2.formula), term1, term2)
                new BinaryTree[SequentOccurrence](SequentOccurrence(
                            createContext(s1.root.antecedent  ++ (s2.root.antecedent - term2)) + prinFormula,
                            createContext((s1.root.succedent - term1) ++ s2.root.succedent)
                        ),
                        s1, s2)
                    with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = ImpLeftRuleType
                        def aux = (term1::Nil)::(term2::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
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
        def apply(s1: LKProof, term1: FormulaOccurrence, term2: FormulaOccurrence) = {
            if (!s1.root.antecedent.contains(term1) || !s1.root.succedent.contains(term2)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Imp(term1.formula, term2.formula), term1, term2)
                new UnaryTree[SequentOccurrence](SequentOccurrence(createContext(s1.root.antecedent - term1), createContext(s1.root.succedent - term1) + prinFormula), s1)
                    with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = ImpRightRuleType
                        def aux = (term1::term2::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
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
        def apply(s1: LKProof, term1: FormulaOccurrence) = {
            if (!s1.root.succedent.contains(term1)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Neg(term1.formula), term1)
                new UnaryTree[SequentOccurrence](SequentOccurrence(createContext(s1.root.antecedent) + prinFormula, createContext(s1.root.succedent - term1)), s1)
                    with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = NegLeftRuleType
                        def aux = (term1::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
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
        def apply(s1: LKProof, term1: FormulaOccurrence) = {
            if (!s1.root.antecedent.contains(term1)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Neg(term1.formula), term1)
                new UnaryTree[SequentOccurrence](SequentOccurrence(createContext(s1.root.antecedent - term1), createContext(s1.root.succedent) + prinFormula), s1)
                    with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = NegRightRuleType
                        def aux = (term1::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        def unapply(proof: LKProof) = if (proof.rule == NegRightRuleType) {
                val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
                val ((a1::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, p1))
            }
            else None
    }
/*
    object ForallLeftRule {
        def apply(s1: LKProof, f: FormulaOccurrence, pos: Position) = {
            if (!s1.root.antecedent.contains(f)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            else {
                val prinFormula = FormulaOccurrence(Neg(term1.formula), term1.label)
                new UnaryTree[SequentOccurrence](SequentOccurrence(s1.root.antecedent - term1, prinFormula :: s1.root.succedent), s1)
                    with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = NegRightRuleType
                        def aux = (term1::Nil)::Nil
                        def prin = prinFormula::Nil
                    }
            }
        }
        def unapply(proof: LKProof) = if (proof.rule == NegRightRuleType) {
                val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
                val ((a1::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.uProof, r.root, a1, p1))
            }
            else None
    }
*/
}
