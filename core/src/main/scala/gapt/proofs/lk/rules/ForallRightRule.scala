package gapt.proofs.lk.rules

import gapt.expr.All
import gapt.expr.BetaReduction
import gapt.expr.Formula
import gapt.expr.Var
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a universal quantifier on the right:
 * <pre>
 *           (π)
 *      Γ :- Δ, A[x\α]
 *     ---------------∀:r
 *      Γ :- Δ, ∀x.A
 * </pre>
 * This rule is only applicable if the eigenvariable condition is satisfied: α must not occur freely in Γ :- Δ.
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\α].
 * @param eigenVariable The variable α.
 * @param quantifiedVariable The variable x.
 */
case class ForallRightRule( subProof: LKProof, aux: SequentIndex, eigenVariable: Var, quantifiedVariable: Var )
  extends UnaryLKProof with CommonRule with Eigenvariable {

  validateIndices( premise, Seq(), Seq( aux ) )

  val ( auxFormula, context ) = premise focus aux

  //eigenvariable condition
  if ( freeVariables( context ) contains eigenVariable )
    throw LKRuleCreationException( s"Eigenvariable condition is violated: $context contains $eigenVariable" )

  val subFormula: Formula = BetaReduction.betaNormalize( Substitution( eigenVariable, quantifiedVariable )( auxFormula ) )

  if ( BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) ) != auxFormula )
    throw LKRuleCreationException(
      s"Aux formula should be $subFormula[$quantifiedVariable\\$eigenVariable] = " +
        BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) ) +
        s", but is $auxFormula." )

  val mainFormula: Formula = BetaReduction.betaNormalize( All( quantifiedVariable, subFormula ) )

  override def name: String = "∀:r"

  def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux ) )

  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}

object ForallRightRule extends ConvenienceConstructor( "ForallRightRule" ) {

  /**
   * Convenience constructor for ∀:r that, given a main formula and an eigenvariable,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A.
   * @param eigenVariable A variable α such that A[α] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula, eigenVariable: Var ): ForallRightRule = {
    if ( freeVariables( mainFormula ) contains eigenVariable ) {
      throw LKRuleCreationException( s"Illegal main formula: Eigenvariable $eigenVariable is free in $mainFormula." )
    } else mainFormula match {
      case All( v, subFormula ) =>
        val auxFormula = Substitution( v, eigenVariable )( subFormula )

        val premise = subProof.endSequent

        val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( auxFormula ) )

        val p = ForallRightRule( subProof, Suc( indices( 0 ) ), eigenVariable, v )
        assert( p.mainFormula == mainFormula )
        p

      case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
    }
  }

  /**
   * Convenience constructor for ∀:r that, given a main formula, will try to construct an inference with that formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A. The premise must contain A.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula ): ForallRightRule = mainFormula match {
    case All( v, _ ) =>
      val p = apply( subProof, mainFormula, v )
      assert( p.mainFormula == mainFormula )
      p

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
  }

  def apply( subProof: LKProof, aux: SequentIndex, mainFormula: Formula, eigenVariable: Var ): ForallRightRule =
    mainFormula match {
      case All( v, _ ) =>
        val p = ForallRightRule( subProof, aux, eigenVariable, v )
        assert( p.mainFormula == mainFormula )
        p
    }
}