package gapt.proofs.lk

import gapt.expr.And
import gapt.expr.Formula
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex

/**
 * An LKProof ending with a conjunction on the left:
 * <pre>
 *         (π)
 *     A, B, Γ :- Δ
 *    --------------
 *    A ∧ B, Γ :- Δ
 * </pre>
 *
 * @param subProof The subproof π.
 * @param aux1 The index of A.
 * @param aux2 The index of B.
 */
case class AndLeftRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex )
  extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux1, aux2 ), Seq() )

  val leftConjunct: Formula = premise( aux1 )
  val rightConjunct: Formula = premise( aux2 )
  val mainFormula: Formula = And( leftConjunct, rightConjunct )

  override def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux1, aux2 ) )

  override def name: String = "∧:l"

  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}

object AndLeftRule extends ConvenienceConstructor( "AndLeftRule" ) {

  /**
   * Convenience constructor for ∧:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param leftConjunct Index of the left conjunct or the conjunct itself.
   * @param rightConjunct Index of the right conjunct or the conjunct itself.
   * @return
   */
  def apply( subProof: LKProof, leftConjunct: IndexOrFormula, rightConjunct: IndexOrFormula ): AndLeftRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( leftConjunct, rightConjunct ), Seq() )

    AndLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ) )
  }

  /**
   * Convenience constructor for ∧:l.
   * Given a proposed main formula A ∧ B, it will attempt to create an inference with this main formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The main formula to be inferred. Must be of the form A ∧ B.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula ): AndLeftRule = mainFormula match {
    case And( f, g ) =>
      val p = apply( subProof, f, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a conjunction." )
  }
}