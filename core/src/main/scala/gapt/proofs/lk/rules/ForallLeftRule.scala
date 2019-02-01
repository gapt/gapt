package gapt.proofs.lk.rules

import gapt.expr.All
import gapt.expr.BetaReduction
import gapt.expr.Expr
import gapt.expr.Formula
import gapt.expr.Substitution
import gapt.expr.Var
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a universal quantifier on the left:
 * <pre>
 *            (π)
 *      A[x\t], Γ :- Δ
 *     ----------------∀:l
 *       ∀x.A, Γ :- Δ
 * </pre>
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\t].
 * @param A The formula A.
 * @param term The term t.
 * @param v The variable x.
 */
case class ForallLeftRule( subProof: LKProof, aux: SequentIndex, A: Formula, term: Expr, v: Var )
  extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux ), Seq() )

  def auxFormula: Formula = premise( aux )
  if ( auxFormula != BetaReduction.betaNormalize( Substitution( v, term )( A ) ) )
    throw LKRuleCreationException( s"Substituting $term for $v in $A does not result in ${premise( aux )}." )

  val mainFormula: Formula = BetaReduction.betaNormalize( All( v, A ) )

  override def name: String = "∀:l"

  def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux ) )

  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}

object ForallLeftRule extends ConvenienceConstructor( "ForallLeftRule" ) {
  /**
   * Convenience constructor for ∀:l that, given a main formula and a term,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A.
   * @param term A term t such that A[t] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula, term: Expr ): ForallLeftRule = {
    val premise = subProof.endSequent

    mainFormula match {
      case All( v, subFormula ) =>
        val auxFormula = BetaReduction.betaNormalize( Substitution( v, term )( subFormula ) )
        val i = premise.antecedent indexOf auxFormula

        if ( i == -1 )
          throw LKRuleCreationException( s"Formula $auxFormula not found in antecedent of $premise." )

        val p = ForallLeftRule( subProof, Ant( i ), subFormula, term, v )
        assert( p.mainFormula == mainFormula )
        p

      case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
    }
  }

  /**
   * Convenience constructor for ∀:l that, given a main formula, will try to construct an inference with that formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A. The premise must contain A.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula ): ForallLeftRule = mainFormula match {
    case All( v, _ ) =>
      val p = apply( subProof, mainFormula, v )
      assert( p.mainFormula == mainFormula )
      p

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
  }

  def apply( subProof: LKProof, aux: SequentIndex, mainFormula: Formula, term: Expr ): ForallLeftRule =
    mainFormula match {
      case All( v, subFormula ) =>
        val p = ForallLeftRule( subProof, aux, subFormula, term, v )
        assert( p.mainFormula == mainFormula )
        p
    }
}