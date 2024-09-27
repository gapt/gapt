package gapt.proofs.lk.rules.macros

import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.WeakeningRightRule

/**
 * Move a formula to the end of the succedent, where the main formula is customarily placed.
 * <pre>
 *          (π)
 *     Γ :- Δ, A, Δ'
 *    --------------
 *     Γ :- Δ, Δ', A
 * </pre>
 */
object ExchangeRightMacroRule {
  def apply(subProof: LKProof, aux: SequentIndex): ContractionRightRule = {
    require(aux isSuc)
    require(subProof.endSequent isDefinedAt aux)
    ContractionRightRule(WeakeningRightRule(subProof, subProof.endSequent(aux)), aux, Suc(subProof.endSequent.succedent.size))
  }
}
