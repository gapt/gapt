package gapt.proofs.lk

import gapt.expr.BetaReduction
import gapt.expr.Ex
import gapt.expr.Expr
import gapt.expr.Formula
import gapt.expr.Substitution
import gapt.expr.Var
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc

/**
 * An LKProof ending with an existential quantifier on the right:
 * <pre>
 *            (π)
 *      Γ :- Δ, A[x\t]
 *     ----------------∃:r
 *       Γ :- Δ, ∃x.A
 * </pre>
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\t].
 * @param A The formula A.
 * @param term The term t.
 * @param v The variable x.
 */
case class ExistsRightRule( subProof: LKProof, aux: SequentIndex, A: Formula, term: Expr, v: Var )
  extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux ) )

  def auxFormula: Formula = premise( aux )
  if ( auxFormula != BetaReduction.betaNormalize( Substitution( v, term )( A ) ) )
    throw LKRuleCreationException( s"Substituting $term for $v in $A does not result in ${premise( aux )}." )

  val mainFormula: Formula = BetaReduction.betaNormalize( Ex( v, A ) )

  override def name: String = "∃:r"

  def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux ) )

  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}

object ExistsRightRule extends ConvenienceConstructor( "ExistsRightRule" ) {

  /**
   * Convenience constructor for ∃:r that, given a main formula and a term,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A.
   * @param term A term t such that A[t] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula, term: Expr ): ExistsRightRule = {
    val premise = subProof.endSequent

    mainFormula match {
      case Ex( v, subFormula ) =>
        val auxFormula = BetaReduction.betaNormalize( Substitution( v, term )( subFormula ) )
        val i = premise.succedent indexOf auxFormula

        if ( i == -1 )
          throw LKRuleCreationException( s"Formula $auxFormula not found in succedent of $premise." )

        val p = ExistsRightRule( subProof, Suc( i ), subFormula, term, v )
        assert( p.mainFormula == mainFormula )
        p

      case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
    }
  }

  /**
   * Convenience constructor for ∃:r that, given a main formula, will try to construct an inference with that formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A. The premise must contain A.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula ): ExistsRightRule = mainFormula match {
    case Ex( v, _ ) =>
      val p = apply( subProof, mainFormula, v )
      assert( p.mainFormula == mainFormula )
      p

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
  }

  def apply( subProof: LKProof, aux: SequentIndex, mainFormula: Formula, term: Expr ): ExistsRightRule =
    mainFormula match {
      case Ex( v, subFormula ) =>
        val p = ExistsRightRule( subProof, aux, subFormula, term, v )
        assert( p.mainFormula == mainFormula )
        p
    }
}