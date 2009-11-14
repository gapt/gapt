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

    case class Sequent[A <: HOL](antecedet: List[Formula[A]], succedent: List[Formula[A]]) {
        override def equals(a: Any) = false // always false as we dont have any way to compare sequents or formula occurrences
    }

    abstract class RuleTypeA
    abstract class NullaryRuleTypeA extends RuleTypeA
    abstract class UnaryRuleTypeA extends RuleTypeA
    abstract class BinaryRuleTypeA extends RuleTypeA
    case object InitialRuleType extends NullaryRuleTypeA
    case object WeakeningLeftRuleType extends UnaryRuleTypeA
    case object AndRightRuleType extends BinaryRuleTypeA

    class LKRuleException(msg: String) extends Exception(msg)
    class LKRuleCreationException(msg: String) extends LKRuleException(msg)
    class FormulaOutOfBoundException(msg: String) extends LKRuleException(msg)

    def idPerm(x: Int) = (x,x)
    
    // rules are extracted in the form (UpperSequent(s), LowerSequent, AuxialiaryFormula(s), PrincipalFormula(s), permutation on lower sequent)
    trait LKProof[A <: HOL] extends Tree[Sequent[A]] {
        def root = vertex
        def rule: RuleTypeA
        def permutation: Int => (Int, Int)
        def antAt(i: Int) = root.antecedet(permutation(i)._1)
        def sucAt(i: Int) = root.succedent(permutation(i)._2)
    }
    trait BinaryLKProof[A <: HOL] extends BinaryTree[Sequent[A]] with LKProof[A] {
        def uProof1 = t1.asInstanceOf[LKProof[A]]
        def uProof2 = t2.asInstanceOf[LKProof[A]]
    }
    trait AuxiliaryFormulas {
        def aux: List[List[Int]]
    }
    trait PrincipalFormulas {
        def prin: List[Int]
    }

    object Axiom {
        var ids = 0
        def apply[A <: HOL](seq: Sequent[A]) =
            new LeafTree[Sequent[A]](seq) with LKProof[A] {def rule = InitialRuleType; def permutation = idPerm}
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == InitialRuleType) Some((proof.root,proof.permutation)) else None
    }

    object AndRightRule {
        def apply[A <: HOL](s1: LKProof[A], s2: LKProof[A], term1: Int, term2: Int) = {
            if (s1.root.succedent.length > term1 && s2.root.succedent.length > term2) {
                new BinaryTree[Sequent[A]](new Sequent(
                            s1.root.antecedet ++ s2.root.antecedet,
                            And(s1.sucAt(term1), s2.sucAt(term2)) :: ((s1.root.succedent - s1.sucAt(term1)) ++ (s2.root.succedent - s2.sucAt(term2)))
                        ),
                        s1, s2)
                    with BinaryLKProof[A] with AuxiliaryFormulas with PrincipalFormulas {
                        def rule = AndRightRuleType
                        def permutation = idPerm
                        def aux = ((term1)::Nil)::(term2::Nil)::Nil
                        def prin = 0::Nil
                    }
            }
            else {
                throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
            }
        } 
        def unapply[A <: HOL](proof: LKProof[A]) = if (proof.rule == AndRightRuleType)
            {
                val r = proof.asInstanceOf[BinaryTree[Sequent[A]] with BinaryLKProof[A] with AuxiliaryFormulas with PrincipalFormulas]
                val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
                val (p1::Nil) = r.prin

                Some((r.uProof1, r.uProof2, r.root, r.uProof1.sucAt(a1), r.uProof2.sucAt(a2), r.sucAt(p1), r.permutation))
            }
            else None
    }

    /*object WeakeningLeftRule {
        def apply[A <: HOL](s1: LKProof[A], s: Sequent[A]) = new UnaryTree[Sequent[A]](s, s1) with LKProof[A] {def rule = WeakeningLeftRuleType}
    }*/
}
