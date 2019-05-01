package gapt.proofs.lk.rules

import gapt.expr.formula.Formula
import gapt.expr.formula.Neg
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof

/**
 * Index of the left cut formula or the formula itself.
 * An LKProof ending with a negation on the left:
 * <pre>
 *       (π)
 *    Γ :- Δ, A
 *   -----------¬:l
 *   ¬A, Γ :- Δ
 * </pre>
 *
 * @param subProof The proof π.
 * @param aux The index of A in the succedent.
 */
case class NegLeftRule( subProof: LKProof, aux: SequentIndex )
  extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux ) )

  def auxFormula: Formula = premise( aux )
  val mainFormula: Formula = Neg( auxFormula )

  override def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux ) )
  override def name: String = "¬:l"

  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}

object NegLeftRule extends ConvenienceConstructor( "NegLeftRule" ) {
  /**
   * Convenience constructor that automatically uses the first occurrence of supplied aux formula.
   *
   * @param subProof The subproof.
   * @param auxFormula The formula to be negated.
   * @return
   */
  def apply( subProof: LKProof, auxFormula: Formula ): NegLeftRule = {
    val premise = subProof.endSequent

    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( auxFormula ) )

    new NegLeftRule( subProof, Suc( indices( 0 ) ) )
  }
}