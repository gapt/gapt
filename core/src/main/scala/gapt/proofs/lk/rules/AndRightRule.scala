package gapt.proofs.lk.rules

import gapt.expr.And
import gapt.expr.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a conjunction on the right:
 * <pre>
 *    (π1)         (π2)
 *   Γ :- Δ, A    Π :- Λ, B
 * --------------------------
 *     Γ, Π :- Δ, Λ, A∧B
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A.
 * @param rightSubProof The proof π,,2,,
 * @param aux2 The index of B.
 */
case class AndRightRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex )
  extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq(), Seq( aux1 ) )
  validateIndices( rightPremise, Seq(), Seq( aux2 ) )

  val leftConjunct: Formula = leftPremise( aux1 )
  val rightConjunct: Formula = rightPremise( aux2 )

  val mainFormula: Formula = And( leftConjunct, rightConjunct )

  def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name: String = "∧:r"

  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}

object AndRightRule extends ConvenienceConstructor( "AndRightRule" ) {

  /**
   * Convenience constructor for ∧:r.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The left subproof.
   * @param leftConjunct Index of the left conjunct or the conjunct itself.
   * @param rightSubProof The right subproof.
   * @param rightConjunct Index of the right conjunct or the conjunct itself.
   * @return
   */
  def apply( leftSubProof: LKProof, leftConjunct: IndexOrFormula,
             rightSubProof: LKProof, rightConjunct: IndexOrFormula ): AndRightRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, leftIndices ) = findAndValidate( leftPremise )( Seq(), Seq( leftConjunct ) )
    val ( _, rightIndices ) = findAndValidate( rightPremise )( Seq(), Seq( rightConjunct ) )

    new AndRightRule( leftSubProof, Suc( leftIndices( 0 ) ), rightSubProof, Suc( rightIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for ∧:r.
   * Given a proposed main formula A ∧ B, it will attempt to create an inference with this main formula.
   *
   * @param leftSubProof The left subproof.
   * @param rightSubProof The right subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A ∧ B.
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof,
             mainFormula: Formula ): AndRightRule = mainFormula match {
    case And( f, g ) =>
      val p = apply( leftSubProof, f, rightSubProof, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a conjunction." )
  }
}