package gapt.proofs.lk.transformations

import gapt.expr.formula.{Atom, Formula}
import gapt.proofs.Sequent
import gapt.proofs.expansion.{ExpansionProofToLK, deskolemizeET}
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.{AndRightRule, ContractionLeftRule, CutRule, EqualityLeftRule, EqualityRightRule, EqualityRule, ForallRightRule, ImpRightRule, LogicalAxiom}
import gapt.provers.escargot.Escargot

object atomicEquality {
  def apply(e: EqualityRule): LKProof =
    if (e.auxFormula.isInstanceOf[Atom])
      e
    else
      e match {
        case EqualityLeftRule(p, _, _, _) =>
          val a = e.auxFormula
          val p0 = lkProof(e.equation +: e.mainFormula +: Sequent() :+ e.auxFormula)
          val p1 = CutRule(p0, p, e.auxFormula)
          ContractionLeftRule(p1, e.equation)
        case EqualityRightRule(p, _, _, _) =>
          val p0 = lkProof(e.equation +: e.auxFormula +: Sequent() :+ e.mainFormula)
          val p1 = CutRule(p, p0, e.auxFormula)
          ContractionLeftRule(p1, e.equation)
      }

  /**
   * A skolem-free LK proof of the provable input sequent with atomic equality inferences.
   */
  private def lkProof(s: Sequent[Formula]): LKProof = {
    val Some(eps) = Escargot.getExpansionProof(s): @unchecked
    val Right(lks) = ExpansionProofToLK(eps): @unchecked
    deskolemizeET(lks)
  }
}
