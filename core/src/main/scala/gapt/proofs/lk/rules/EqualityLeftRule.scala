package gapt.proofs.lk.rules

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.BetaReduction
import gapt.expr.Eq
import gapt.expr.Formula
import gapt.expr.replacementContext
import gapt.proofs.Ant
import gapt.proofs.HOLSequent
import gapt.proofs.IndexOrFormula
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with a left equality rule.
 * There are two possible cases according to which direction the rule is applied in:
 *
 * <pre>
 *            (π)                            (π)
 *    A[s], s = t, Γ :- Δ            A[t], s = t, Γ :- Δ
 *   ---------------------eq:l      ---------------------eq:l
 *    A[t], s = t, Γ :- Δ            A[s], s = t, Γ :- Δ
 *
 * </pre>
 *
 * @param subProof The subproof π.
 * @param eq The index of s = t.
 * @param aux The index of the formula in which the replacement is to be performed.
 * @param replacementContext A term λx.A[x] that designates the positions to be replaced.
 */
case class EqualityLeftRule( subProof: LKProof, eq: SequentIndex, aux: SequentIndex, replacementContext: Abs )
  extends EqualityRule {

  validateIndices( premise, Seq( eq, aux ), Seq() )

  override def name: String = "eq:l"

  override def mainFormulaSequent: HOLSequent = mainFormula +: Sequent()
}

object EqualityLeftRule extends ConvenienceConstructor( "EqualityLeftRule" ) {

  /**
   * Convenience constructor for eq:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param eqFormula The index of the equation or the equation itself.
   * @param auxFormula The index of the auxiliary formula or the formula itself.
   * @param replacementContext A term λx.A[x] that designates the positions to be replaced.
   * @return
   */
  def apply( subProof: LKProof, eqFormula: IndexOrFormula, auxFormula: IndexOrFormula,
             replacementContext: Abs ): EqualityLeftRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( eqFormula, auxFormula ), Seq() )

    EqualityLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ), replacementContext )

  }

  /**
   * Convenience constructor for eq:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param eq The index of the equation or the equation itself.
   * @param aux The index of the auxiliary formula or the formula itself.
   * @param mainFormula The proposed main formula.
   * @return
   */
  def apply( subProof: LKProof, eq: IndexOrFormula, aux: IndexOrFormula, mainFormula: Formula ): EqualityLeftRule = {
    val premise = subProof.endSequent
    val ( indices, _ ) = findAndValidate( premise )( Seq( eq, aux ), Seq() )
    val ( eqFormula, auxFormula ) = ( premise( Ant( indices( 0 ) ) ), premise( Ant( indices( 1 ) ) ) )

    eqFormula match {
      case Eq( s, t ) =>
        if ( s == t && auxFormula == mainFormula ) {
          val repContext = replacementContext.abstractTerm( auxFormula )( s )

          val Abs( _, _ ) = repContext
          if ( auxFormula.find( s ).isEmpty )
            throw LKRuleCreationException( s"Eq is trivial, but term $s does not occur in $auxFormula." )

          EqualityLeftRule( subProof, eq, aux, repContext )

        } else if ( s == t && auxFormula != mainFormula ) {
          throw LKRuleCreationException(
            s"Eq is trivial, but aux formula $auxFormula and main formula $mainFormula differ." )

        } else if ( s != t && auxFormula == mainFormula ) {
          throw LKRuleCreationException( "Nontrivial equation, but aux and main formula are equal." )

        } else {
          val contextS = replacementContext( s.ty, auxFormula, auxFormula.find( s ) intersect mainFormula.find( t ) )
          val contextT = replacementContext( t.ty, auxFormula, auxFormula.find( t ) intersect mainFormula.find( s ) )

          val Abs( vS, restS ) = contextS
          val Abs( vT, restT ) = contextT

          if ( restS.find( vS ).isEmpty && restT.find( vT ).isEmpty )
            throw LKRuleCreationException( s"Neither $s nor $t found in formula $auxFormula." )

          val p = if ( BetaReduction.betaNormalize( App( contextS, t ) ) ==
            BetaReduction.betaNormalize( mainFormula ) ) {
            EqualityLeftRule( subProof, eq, aux, contextS )
          } else if ( BetaReduction.betaNormalize( App( contextT, s ) ) ==
            BetaReduction.betaNormalize( mainFormula ) ) {
            EqualityLeftRule( subProof, eq, aux, contextT )
          } else throw LKRuleCreationException( "Replacement in neither direction leads to proposed main formula." )

          assert( p.mainFormula == mainFormula )
          p
        }

      case _ => throw LKRuleCreationException( s"Formula $eqFormula is not an equation." )
    }
  }
}