package gapt.proofs.lk.rules

import gapt.expr.Formula
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a conversion on the left.
 *
 * <pre>
 *       (π)
 *    N, Γ :- Δ
 *   -----------d:l
 *    M, Γ :- Δ
 * </pre>
 *
 * LK proofs that contain this rule are not sound by construction, since it allows you to replace any formula
 * by any other formula. The soundness of such proofs can only be established with respect to a context in which we have
 * M =βδ N. Use the `check` method on [[gapt.proofs.context.Context]] to check whether the constructed proof is sound.
 *
 * @param subProof The proof π.
 * @param aux The index of N in the antecedent.
 * @param mainFormula The formula N.
 */
case class ConversionLeftRule( subProof: LKProof, aux: SequentIndex, mainFormula: Formula ) extends ConversionRule {
  override def name: String = "conv:l"
  override def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux ) )
  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}

object ConversionLeftRule extends ConvenienceConstructor( "ConversionLeftRule" ) {

  /**
   * Constructs a derivation ending in a conversion left rule.
   *
   * Constructs a derivation of the form:
   *
   * <pre>
   *       (π)
   *    M, Γ :- Δ
   *   -----------conv:l
   *    N, Γ :- Δ.
   * </pre>
   *
   * @param subProof The subproof π.
   * @param aux The auxiliary formula M or its index in the antecedent.
   * @param mainFormula The main formula N.
   */
  def apply( subProof: LKProof, aux: IndexOrFormula, mainFormula: Formula ): ConversionLeftRule = {
    val premise = subProof.endSequent
    val ( indices, _ ) = findAndValidate( premise )( Seq( aux ), Seq() )

    ConversionLeftRule( subProof, Ant( indices( 0 ) ), mainFormula )
  }
}