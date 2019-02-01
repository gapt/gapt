package gapt.proofs.lk.rules.macros

import gapt.proofs.Ant
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.WeakeningLeftRule

/**
 * Move a formula to the beginning of the antecedent, where the main formula is customarily placed.
 * <pre>
 *          (π)
 *     Γ, A, Γ' :- Δ
 *    --------------
 *     A, Γ, Γ' :- Δ
 * </pre>
 */
object ExchangeLeftMacroRule {
  def apply( subProof: LKProof, aux: SequentIndex ): ContractionLeftRule = {
    require( aux isAnt )
    require( subProof.endSequent isDefinedAt aux )
    ContractionLeftRule( WeakeningLeftRule( subProof, subProof.endSequent( aux ) ), Ant( 0 ), aux + 1 )
  }
}
