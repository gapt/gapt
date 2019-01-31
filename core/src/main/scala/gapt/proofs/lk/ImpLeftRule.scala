package gapt.proofs.lk

import gapt.expr.Formula
import gapt.expr.Imp
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc

/**
 * An LKProof ending with an implication on the left:
 * <pre>
 *     (π1)         (π2)
 *   Γ :- Δ, A    B, Π :- Λ
 * --------------------------
 *     A→B, Γ, Π :- Δ, Λ
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A.
 * @param rightSubProof The proof π,,2,,
 * @param aux2 The index of B.
 */
case class ImpLeftRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex )
  extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq(), Seq( aux1 ) )
  validateIndices( rightPremise, Seq( aux2 ), Seq() )

  val impPremise: Formula = leftPremise( aux1 )
  val impConclusion: Formula = rightPremise( aux2 )

  val mainFormula: Formula = Imp( impPremise, impConclusion )

  def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name: String = "→:l"

  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}

object ImpLeftRule extends ConvenienceConstructor( "ImpLeftRule" ) {

  /**
   * Convenience constructor for →:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The left subproof.
   * @param impPremise Index of the premise of the implication or the premise itself.
   * @param rightSubProof The right subproof.
   * @param impConclusion Index of the conclusion of the implication or the conclusion itself.
   * @return
   */
  def apply( leftSubProof: LKProof, impPremise: IndexOrFormula,
             rightSubProof: LKProof, impConclusion: IndexOrFormula ): ImpLeftRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, leftIndices ) = findAndValidate( leftPremise )( Seq(), Seq( impPremise ) )
    val ( rightIndices, _ ) = findAndValidate( rightPremise )( Seq( impConclusion ), Seq() )

    new ImpLeftRule( leftSubProof, Suc( leftIndices( 0 ) ), rightSubProof, Ant( rightIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for →:l.
   * Given a proposed main formula A → B, it will attempt to create an inference with this main formula.
   *
   * @param leftSubProof The left subproof.
   * @param rightSubProof The right subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A → B.
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, mainFormula: Formula ): ImpLeftRule = mainFormula match {
    case Imp( f, g ) =>
      val p = apply( leftSubProof, f, rightSubProof, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a implication." )
  }
}