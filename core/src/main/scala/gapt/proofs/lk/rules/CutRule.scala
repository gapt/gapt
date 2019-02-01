package gapt.proofs.lk.rules

import gapt.expr.Formula
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a cut:
 * <pre>
 *      (π1)         (π2)
 *    Γ :- Δ, A   A, Π :- Λ
 *   ------------------------
 *        Γ, Π :- Δ, Λ
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A in π,,1,,.
 * @param rightSubProof The proof π,,2,,.
 * @param aux2 The index of A in π,,2,,.
 */
case class CutRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex )
  extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq(), Seq( aux1 ) )
  validateIndices( rightPremise, Seq( aux2 ), Seq() )

  if ( leftPremise( aux1 ) != rightPremise( aux2 ) )
    throw LKRuleCreationException(
      s"Auxiliary formulas are not the same:\n${leftPremise( aux1 )}\n${rightPremise( aux2 )}" )

  def cutFormula: Formula = leftPremise( aux1 )

  override def name: String = "cut"

  def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def mainFormulaSequent: HOLSequent = Sequent()
}

object CutRule extends ConvenienceConstructor( "CutRule" ) {

  /**
   * Convenience constructor for cut.
   * Each of the cut formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The left subproof.
   * @param leftCutFormula Index of the left cut formula or the formula itself.
   * @param rightSubProof The right subproof.
   * @param rightCutFormula Index of the right cut formula or the formula itself.
   * @return
   */
  def apply( leftSubProof: LKProof, leftCutFormula: IndexOrFormula,
             rightSubProof: LKProof, rightCutFormula: IndexOrFormula ): CutRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, sucIndices ) = findAndValidate( leftPremise )( Seq(), Seq( leftCutFormula ) )
    val ( antIndices, _ ) = findAndValidate( rightPremise )( Seq( rightCutFormula ), Seq() )

    new CutRule( leftSubProof, Suc( sucIndices( 0 ) ), rightSubProof, Ant( antIndices( 0 ) ) )

  }

  /**
   * Convenience constructor for cut.
   * Given a cut formula, it will attempt to create a cut inference with that formula.
   *
   * @param leftSubProof The left subproof.
   * @param rightSubProof The right subproof.
   * @param cutFormula The cut formula.
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, cutFormula: Formula ): CutRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, sucIndices ) = findAndValidate( leftPremise )( Seq(), Seq( cutFormula ) )
    val ( antIndices, _ ) = findAndValidate( rightPremise )( Seq( cutFormula ), Seq() )

    new CutRule( leftSubProof, Suc( sucIndices( 0 ) ), rightSubProof, Ant( antIndices( 0 ) ) )
  }
}