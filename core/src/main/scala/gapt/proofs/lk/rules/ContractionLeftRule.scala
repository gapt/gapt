package gapt.proofs.lk.rules

import gapt.expr.formula.Formula
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a left contraction:
 * <pre>
 *         (π)
 *     A, A, Γ :- Δ
 *    --------------
 *      A, Γ :- Δ
 * </pre>
 *
 * @param subProof The subproof π.
 * @param aux1 The index of one occurrence of A.
 * @param aux2 The index of the other occurrence of A.
 */
case class ContractionLeftRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends ContractionRule {

  validateIndices( premise, Seq( aux1, aux2 ), Seq() )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw LKRuleCreationException( s"Auxiliary formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )

  override def name: String = "c:l"

  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}

object ContractionLeftRule extends ConvenienceConstructor( "ContractionLeftRule" ) {
  /**
   * Convenience constructor for c:l that, given a formula to contract on the left,
   * will automatically pick the first two occurrences of that formula.
   *
   * @param subProof The subproof π.
   * @param f The formula to contract.
   * @return
   */
  def apply( subProof: LKProof, f: Formula ): ContractionLeftRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( f, f ), Seq() )

    val p = ContractionLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ) )
    assert( p.mainFormula == f )
    p
  }

}