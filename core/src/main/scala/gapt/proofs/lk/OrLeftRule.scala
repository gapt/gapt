package gapt.proofs.lk

import gapt.expr.Formula
import gapt.expr.Or
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex

/**
 * An LKProof ending with a disjunction on the left:
 * <pre>
 *     (π1)         (π2)
 *   A, Γ :- Δ    B, Π :- Λ
 * --------------------------
 *     A∨B, Γ, Π :- Δ, Λ
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A.
 * @param rightSubProof The proof π,,2,,
 * @param aux2 The index of B.
 */
case class OrLeftRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex )
  extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq( aux1 ), Seq() )
  validateIndices( rightPremise, Seq( aux2 ), Seq() )

  val leftDisjunct: Formula = leftPremise( aux1 )
  val rightDisjunct: Formula = rightPremise( aux2 )

  val mainFormula: Formula = Or( leftDisjunct, rightDisjunct )

  def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name: String = "∨:l"

  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}

object OrLeftRule extends ConvenienceConstructor( "OrLeftRule" ) {

  /**
   * Convenience constructor for ∨:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The left subproof.
   * @param leftDisjunct Index of the left disjunct or the disjunct itself.
   * @param rightSubProof The right subproof.
   * @param rightDisjunct Index of the right disjunct or the disjunct itself.
   * @return
   */
  def apply( leftSubProof: LKProof, leftDisjunct: IndexOrFormula,
             rightSubProof: LKProof, rightDisjunct: IndexOrFormula ): OrLeftRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( leftIndices, _ ) = findAndValidate( leftPremise )( Seq( leftDisjunct ), Seq() )
    val ( rightIndices, _ ) = findAndValidate( rightPremise )( Seq( rightDisjunct ), Seq() )

    new OrLeftRule( leftSubProof, Ant( leftIndices( 0 ) ), rightSubProof, Ant( rightIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for ∨:r.
   * Given a proposed main formula A ∨ B, it will attempt to create an inference with this main formula.
   *
   * @param leftSubProof The left subproof.
   * @param rightSubProof The right subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A ∨ B.
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, mainFormula: Formula ): OrLeftRule = mainFormula match {
    case Or( f, g ) =>
      val p = apply( leftSubProof, f, rightSubProof, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a disjunction." )
  }
}