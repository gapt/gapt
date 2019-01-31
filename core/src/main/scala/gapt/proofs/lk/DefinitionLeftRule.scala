package gapt.proofs.lk

import gapt.expr.Formula
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex

/**
 * An LKProof ending with a definition on the left.
 *
 * Introducing the definition c := φ on the left means replacing some occurrences of the expression φ by c in a
 * formula in the antecedent:
 *
 * <pre>
 *       (π)
 *    A[φ], Γ :- Δ
 *   -----------d:l
 *    A[c], Γ :- Δ
 * </pre>
 *
 * NB: LK proofs that contain this rule are not sound by construction, since it allows you to replace any formula
 * by any other formula. The soundness of such proofs can only be established with respect to a Context.
 * Use the `check` method on [[gapt.proofs.context.Context]] to check whether the constructed proof is sound.
 *
 * @param subProof The proof π.
 * @param aux The index of A in the antecedent.
 * @param mainFormula The formula
 */
case class DefinitionLeftRule( subProof: LKProof, aux: SequentIndex, mainFormula: Formula ) extends DefinitionRule {
  override def name: String = "d:l"
  override def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux ) )
  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}

object DefinitionLeftRule extends ConvenienceConstructor( "DefinitionLeftRule" ) {

  /**
   * Convenience constructor for d:l.
   *
   * @param subProof The subproof.
   * @param aux The aux formula or its index.
   * @param mainFormula The main formula.
   */
  def apply( subProof: LKProof, aux: IndexOrFormula, mainFormula: Formula ): DefinitionLeftRule = {
    val premise = subProof.endSequent
    val ( indices, _ ) = findAndValidate( premise )( Seq( aux ), Seq() )

    DefinitionLeftRule( subProof, Ant( indices( 0 ) ), mainFormula )
  }
}