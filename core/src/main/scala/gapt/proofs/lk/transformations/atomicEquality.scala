package gapt.proofs.lk.transformations

import gapt.expr.formula.{Atom, Formula}
import gapt.proofs.Sequent
import gapt.proofs.expansion.{ExpansionProofToLK, deskolemizeET}
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.{ContractionLeftRule, CutRule, EqualityLeftRule, EqualityRightRule, EqualityRule}
import gapt.provers.escargot.Escargot

/**
 * Replaces an equality inferences with non-atomic main and auxiliary formula
 * by a cut whose new subproof introduces only equality inferences with atomic
 * main and auxiliary formulas.
 **/
object atomicEquality {
  def apply(e: EqualityRule): LKProof =
    if (e.auxFormula.isInstanceOf[Atom])
      e
    else
      e match {
        case EqualityLeftRule(p, _, _, _) =>
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
