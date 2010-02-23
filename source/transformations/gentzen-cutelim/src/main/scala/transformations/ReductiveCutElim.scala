/*
 * ReductiveCutElim.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations

import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.base._
import at.logic.language.hol._
import at.logic.calculi.occurrences._

/*object ReductiveCutElim {

  def cutElim(proof: LKProof): LKProof = proof match {
    case Axiom(_) => proof
    case WeakeningLeftRule(up, _, pf) => WeakeningLeftRule(cutElim(up), pf.formula)
    case WeakeningRightRule(up, _, pf) => WeakeningRightRule(cutElim(up), pf.formula)
    case ContractionLeftRule(up, _, aux1, aux2, _) => ContractionLeftRule(cutElim(up), aux1, aux2)
    case ContractionRightRule(up, _, aux1, aux2, _) => ContractionRightRule(cutElim(up), aux1, aux2)
    case AndRightRule(up1, up2, _, aux1, aux2, _) => AndRightRule(cutElim(up1), cutElim(up2), aux1, aux2)
    case AndLeft1Rule(up, _, aux, FormulaOccurrence(And(_, f),_,_)) => AndLeft1Rule(cutElim(up), aux, f)
    case AndLeft2Rule(up, _, aux, FormulaOccurrence(And(f, _),_,_)) => AndLeft2Rule(cutElim(up), f, aux)
    case OrLeftRule(up1, up2, _, aux1, aux2, _) => OrLeftRule(cutElim(up1), cutElim(up2), aux1, aux2)
    case OrRight1Rule(up, _, aux, FormulaOccurrence(Or(_, f),_,_)) => OrRight1Rule(cutElim(up), aux, f)
    case OrRight2Rule(up, _, aux, FormulaOccurrence(Or(f, _),_,_)) => OrRight2Rule(cutElim(up), f, aux)
    case ImpLeftRule(up1, up2, _, aux1, aux2, _) => ImpLeftRule(cutElim(up1), cutElim(up2), aux1, aux2)
    case ImpRightRule(up, _, aux1, aux2, _) => ImpRightRule(cutElim(up), aux1, aux2)
    case NegLeftRule(up, _, aux, _) => NegLeftRule(cutElim(up), aux)
    case NegRightRule(up, _, aux, _) => NegRightRule(cutElim(up), aux)
    case CutRule(up1, up2, root, a1, a2) => {
      val proof1 = cutElim(up1)
      val proof2 = cutElim(up2)
      /*val rank1 = rank(proof1, a1, false)
      val rank2 = rank(proof2, a2, true)*/
      proof
    }
  }

    /*def rank[A <: HOL](proof: LKProof[A], fo: FormulaOccurrence[A], ant: Boolean) = proof match {
        case InitialRule()
    }*/
}
*/