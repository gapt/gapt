package gapt.proofs.lk

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
import gapt.proofs.Suc

/**
 * An LKProof ending with a right equality rule.
 * There are two possible cases according to which direction the rule is applied in:
 *
 * <pre>
 *            (π)                            (π)
 *    s = t, Γ :- Δ, A[s]            s = t, Γ :- Δ, A[t]
 *   ---------------------eq:r      ---------------------eq:r
 *    s = t, Γ :- Δ, A[t]            s = t, Γ :- Δ, A[s]
 * </pre>
 *
 * @param subProof The subproof π.
 * @param eq The index of s = t.
 * @param aux The index of the formula in which the replacement is to be performed.
 * @param replacementContext A term λx.A[x] that designates the positions to be replaced.
 */
case class EqualityRightRule( subProof: LKProof, eq: SequentIndex, aux: SequentIndex, replacementContext: Abs )
  extends EqualityRule {

  validateIndices( premise, Seq( eq ), Seq( aux ) )

  override def name: String = "eq:r"

  override def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
}

object EqualityRightRule extends ConvenienceConstructor( "EqualityRightRule" ) {

  /**
   * Convenience constructor for eq:r.
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
             replacementContext: Abs ): EqualityRightRule = {
    val premise = subProof.endSequent

    val ( indicesAnt, indicesSuc ) = findAndValidate( premise )( Seq( eqFormula ), Seq( auxFormula ) )

    EqualityRightRule( subProof, Ant( indicesAnt( 0 ) ), Suc( indicesSuc( 0 ) ), replacementContext )

  }

  /**
   * Convenience constructor for eq:r.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param eq The index of the equation or the equation itself.
   * @param aux The index of the auxiliary formula or the formula itself.
   * @param mainFormula The proposed main formula.
   * @return
   */
  def apply( subProof: LKProof, eq: IndexOrFormula, aux: IndexOrFormula, mainFormula: Formula ): EqualityRightRule = {
    val premise = subProof.endSequent
    val ( indicesAnt, indicesSuc ) = findAndValidate( premise )( Seq( eq ), Seq( aux ) )
    val ( eqFormula, auxFormula ) = ( premise( Ant( indicesAnt( 0 ) ) ), premise( Suc( indicesSuc( 0 ) ) ) )

    eqFormula match {
      case Eq( s, t ) =>
        if ( s == t && auxFormula == mainFormula ) {
          val repContext = replacementContext.abstractTerm( auxFormula )( s )

          val Abs( _, _ ) = repContext
          if ( auxFormula.find( s ).isEmpty )
            throw LKRuleCreationException( s"Eq is trivial, but term $s does not occur in $auxFormula." )

          EqualityRightRule( subProof, eq, aux, repContext )

        } else if ( s == t && auxFormula != mainFormula ) {
          throw LKRuleCreationException( s"Eq is trivial, but aux formula $auxFormula and main formula $mainFormula." )

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
            EqualityRightRule( subProof, eq, aux, contextS )
          } else if ( BetaReduction.betaNormalize( App( contextT, s ) ) ==
            BetaReduction.betaNormalize( mainFormula ) ) {
            EqualityRightRule( subProof, eq, aux, contextT )
          } else throw LKRuleCreationException( "Replacement in neither direction leads to proposed main formula." )

          assert( p.mainFormula == mainFormula )
          p
        }

      case _ => throw LKRuleCreationException( s"Formula $eqFormula is not an equation." )
    }
  }
}