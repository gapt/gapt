package gapt.proofs.lk.rules

import gapt.expr.Apps
import gapt.expr.BetaReduction
import gapt.expr.Expr
import gapt.expr.formula.All
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.instantiate
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a universal quantifier on the right:
 * <pre>
 *           (π)
 *      Γ :- Δ, A[x\s(...)]
 *     ---------------∀:r
 *      Γ :- Δ, ∀x.A
 * </pre>
 * This rule requires a Skolem function s(...)
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\α].
 * @param mainFormula The main formula A[x\s(...)]
 * @param skolemTerm The Skolem term s(...)
 */
case class ForallSkRightRule( subProof: LKProof, aux: SequentIndex, mainFormula: Formula,
                              skolemTerm: Expr )
  extends SkolemQuantifierRule {

  validateIndices( premise, Seq(), Seq( aux ) )

  val All( quantifiedVariable, subFormula ) = mainFormula: @unchecked

  override def name: String = "∀sk:r"

  def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux ) )

  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}

object ForallSkRightRule extends ConvenienceConstructor( "ForallSkRightRule" ) {

  /**
   * Convenience constructor for ∀sk:r that, given a Skolem term and Skolem definition,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @return
   */
  def apply( subProof: LKProof, skolemTerm: Expr, skolemDef: Expr ): ForallSkRightRule = {
    val Apps( _, skolemArgs ) = skolemTerm
    val mainFormula = BetaReduction.betaNormalize( skolemDef( skolemArgs: _* ) ).asInstanceOf[Formula]
    apply( subProof, mainFormula, skolemTerm )
  }

  def apply( subProof: LKProof, mainFormula: Formula, skolemTerm: Expr ): ForallSkRightRule = {
    val auxFormula = instantiate( mainFormula, skolemTerm )
    val premise = subProof.endSequent
    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( auxFormula ) )
    ForallSkRightRule( subProof, Suc( indices( 0 ) ), mainFormula, skolemTerm )
  }
}