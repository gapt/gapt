package gapt.proofs.lk

import gapt.expr.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc

/**
 * An LKProof ending with a definition on the right.
 *
 * Introducing the definition c := φ on the right means replacing some occurrences of the expression φ by c in a
 * formula in the succedent:
 *
 * <pre>
 *       (π)
 *    Γ :- Δ, A[φ]
 *   -----------d:r
 *    Γ :- Δ, A[c]
 * </pre>
 *
 * NB: LK proofs that contain this rule are not sound by construction, since it allows you to replace any formula
 * by any other formula. The soundness of such proofs can only be established with respect to a Context.
 * Use the `check` method on [[gapt.proofs.context.Context]] to check whether the constructed proof is sound.
 *
 * @param subProof The proof π.
 * @param aux The index of A in the succedent.
 * @param mainFormula The formula
 */
case class DefinitionRightRule( subProof: LKProof, aux: SequentIndex, mainFormula: Formula ) extends DefinitionRule {
  override def name: String = "d:r"
  override def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux ) )
  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}

object DefinitionRightRule extends ConvenienceConstructor( "DefinitionRightRule" ) {

  /**
   * Convenience constructor for d:r.
   *
   * @param subProof The subproof.
   * @param aux The aux formula or its index.
   * @param mainFormula The main formula.
   */
  def apply( subProof: LKProof, aux: IndexOrFormula, mainFormula: Formula ): DefinitionRightRule = {
    val premise = subProof.endSequent
    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( aux ) )

    DefinitionRightRule( subProof, Suc( indices( 0 ) ), mainFormula )
  }
}