/*
 * LK.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import ExpressionOccurrences._
import at.logic.language.hol.HigherOrderLogic._
import at.logic.utils.ds.Trees._
import scala.collection.immutable.{Set, EmptySet}

object LK {

    case class Sequent[A <: HOL](antecedet: Set[FormulaOccurrence[A]], succedent: Set[FormulaOccurrence[HOL]])

    abstract class RuleTypeA
    abstract class NullaryRuleTypeA extends RuleTypeA
    abstract class UnaryRuleTypeA extends RuleTypeA
    abstract class BinaryRuleTypeA extends RuleTypeA
    case object InitialRuleType extends NullaryRuleTypeA
    case object WeakeningLeftRuleType extends UnaryRuleTypeA
    case object AndRightRuleType extends BinaryRuleTypeA

    class LKRuleCreationException(msg: String) extends Exception(msg)
    
    // rules are extracted in the form (UpperSequent(s), LowerSequent, AuxialiaryFormula(s), PrincipalFormula(s))
    trait LKProof[A <: HOL] extends Tree[Sequent[A]] {
        def root = vertex
        def rule: RuleTypeA
    }
    trait AuxiliaryFormulas[A <: HOL] {
        def aux: List[FormulaOccurrence[A]]
    }
    trait PrincipalFormulas[A <: HOL] {
        def prin: List[FormulaOccurrence[A]]
    }

    object Axiom {
        var ids = 0
        def apply[A <: HOL](antecedet: Set[Formula[A]], succedent: Set[Formula[A]]) =
            new LeafTree[Sequent[A]](Sequent(antecedet.map(createOccurrence[A]), succedent.map(createOccurrence[A]))) with LKProof[A] {def rule = InitialRuleType}
        def createOccurrence[A <: HOL](f: Formula[A]): FormulaOccurrence[A] = { ids = ids + 1; FormulaOccurrence[A](f, BaseOccur[Int](ids)) }
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == InitialRuleType)
            {
                val r = proof.asInstanceOf[LeafTree[Sequent[A]] with LKProof[A]]
                Some((r.root))
            }
            else None
    }

    object AndRightRule {
        def apply[A <: HOL](s1: LKProof[A], s2: LKProof[A], term1: FormulaOccurrence[A], term2: FormulaOccurrence[A]) = {
            if (s1.root.succedent.contains(term1) && s2.root.succedent.contains(term2)) {
                val prinFormula = FormulaOccurrence(And(term1.formula, term2.formula), term1.merge(term2))
                new BinaryTree[Sequent[A]](createRoot(prinFormula, term1, term2, s1.root, s2.root), s1, s2) with LKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]
                    {def rule = AndRightRuleType; def aux = term1::term2::Nil; def prin = prinFormula::Nil}
            }
            else {
                throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            }
        }
        def createRoot[A <: HOL](prinFormula: FormulaOccurrence[A], t1: FormulaOccurrence[A], t2: FormulaOccurrence[A], s1: Sequent[A], s2: Sequent[A]) =
            new Sequent(s1.antecedet ++ s2.antecedet, (s1.succedent - t1) ++ (s2.succedent - t2) + prinFormula)
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == AndRightRuleType)
            {
                val r = proof.asInstanceOf[BinaryTree[Sequent[A]] with LKProof[A] with AuxiliaryFormulas[A] with PrincipalFormulas[A]]
                val (a1::a2::Nil) = r.aux
                val (p1::Nil) = r.prin
                Some((r.t1, r.t2, r.root, a1, a2, p1))
            }
            else None
    }

    /*object WeakeningLeftRule {
        def apply[A <: HOL](s1: LKProof[A], s: Sequent[A]) = new UnaryTree[Sequent[A]](s, s1) with LKProof[A] {def rule = WeakeningLeftRuleType}
    }*/
}
