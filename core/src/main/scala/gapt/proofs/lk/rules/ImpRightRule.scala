package gapt.proofs.lk.rules

import gapt.expr.Formula
import gapt.expr.Imp
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with an implication on the right:
 * <pre>
 *         (π)
 *     A, Γ :- Δ, B
 *    --------------
 *     Γ :- Δ, A → B
 * </pre>
 *
 * @param subProof The subproof π.
 * @param aux1 The index of A.
 * @param aux2 The index of B.
 */
case class ImpRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex )
  extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux1 ), Seq( aux2 ) )

  val impPremise: Formula = premise( aux1 )
  val impConclusion: Formula = premise( aux2 )
  val mainFormula: Formula = Imp( impPremise, impConclusion )

  override def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux1, aux2 ) )

  override def name: String = "→:r"

  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}

object ImpRightRule extends ConvenienceConstructor( "ImpRightRule" ) {

  /**
   * Convenience constructor for →:r.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param impPremise Index of the premise of the implication or the premise itself.
   * @param impConclusion Index of the conclusion of the implication or the conclusion itself.
   * @return
   */
  def apply( subProof: LKProof, impPremise: IndexOrFormula, impConclusion: IndexOrFormula ): ImpRightRule = {
    val premise = subProof.endSequent

    val ( antIndices, sucIndices ) = findAndValidate( premise )( Seq( impPremise ), Seq( impConclusion ) )

    new ImpRightRule( subProof, Ant( antIndices( 0 ) ), Suc( sucIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for →:r that, given a proposed main formula A → B,
   * will attempt to create an inference with this main formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A → B.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula ): ImpRightRule = mainFormula match {
    case Imp( f, g ) =>
      val p = apply( subProof, f, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not an implication." )
  }
}