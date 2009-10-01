/*
 * Description: generic LK sequent calculus (for any order)
**/

package at.logic.syntax.calculus.lk

import at.logic.syntax.calculus
import at.logic.syntax.language.{FunctionA,OType}

case object Axiom extends NullaryRuleTypeA
case object ForallLeft extends UnaryRuleTypeA
case class FormulaOccurrence(f : FunctionA[OType]) extends TermOccurrence(f)
case class Sequent(ant : List[FormulaOccurrence], suc : List[FormulaOccurrence]) extends SequentA(ant,suc)

trait LkProof[+T <: RuleA] extends RuleA{
    this: T with LkProof[T] =>
}

final case class AxiomRule(s : Sequent) extends NullaryRuleA(Axiom,s) with LkProof[AxiomRule]
final case class ForallLeftRule(u : LkProof[RuleA], c2 : Sequent, a2 : FormulaOccurrence, p2 : FormulaOccurrence) extends UnaryRuleA(ForallLeft, u, c2, Some(List[FormulaOccurrence](a2)), Some(List[FormulaOccurrence](p2))) with LkProof[ForallLeftRule]
