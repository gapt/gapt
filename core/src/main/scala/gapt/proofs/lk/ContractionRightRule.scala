package gapt.proofs.lk

import gapt.expr.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc

/**
 * An LKProof ending with a right contraction:
 * <pre>
 *         (π)
 *     Γ :- Δ, A, A
 *    --------------
 *      Γ :- Δ, A
 * </pre>
 *
 * @param subProof The subproof π.
 * @param aux1 The index of one occurrence of A.
 * @param aux2 The index of the other occurrence of A.
 */
case class ContractionRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends ContractionRule {

  validateIndices( premise, Seq(), Seq( aux1, aux2 ) )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw LKRuleCreationException( s"Auxiliary formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )

  override def name: String = "c:r"

  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula

}

object ContractionRightRule extends ConvenienceConstructor( "ContractionRightRule" ) {
  /**
   * Convenience constructor for c:r that, given a formula to contract on the right,
   * will automatically pick the first two occurrences of that formula.
   *
   * @param subProof The subproof π.
   * @param f The formula to contract.
   * @return
   */
  def apply( subProof: LKProof, f: Formula ): ContractionRightRule = {
    val premise = subProof.endSequent

    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( f, f ) )
    val p = ContractionRightRule( subProof, Suc( indices( 0 ) ), Suc( indices( 1 ) ) )
    assert( p.mainFormula == f )
    p
  }

}