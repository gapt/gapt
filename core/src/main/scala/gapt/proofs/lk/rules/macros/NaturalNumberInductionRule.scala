package gapt.proofs.lk.rules.macros

import gapt.expr.Abs
import gapt.expr.formula.All
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.util.syntacticMatching
import gapt.proofs.Ant
import gapt.proofs.IndexOrFormula
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ConvenienceConstructor
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.InductionCase
import gapt.proofs.lk.rules.InductionRule

object NaturalNumberInductionRule extends ConvenienceConstructor( "NaturalNumberInductionRule" ) {
  /**
   * An LKProof ending with an induction over the natural numbers:
   *
   * <pre>
   *      (π1)                (π2)
   *  Γ :- Δ, A[0]    A[y], Π :- Λ, A[y]
   * ------------------------------------ind
   *           Γ, Π :- Δ, Λ, ∀x. A[x]
   * </pre>
   * Note that there is an eigenvariable condition on x, i.e. x must not occur freely in Π :- Λ.
   *
   * @param leftSubProof The subproof π,,1,,
   * @param aux1 The index of A[0].
   * @param rightSubProof The subproof π,,2,,
   * @param aux2 The index of A[y].
   * @param aux3 The index of A[sy].
   * @param mainFormula The formula ∀x. A[x].
   */
  def apply( leftSubProof: LKProof, aux1: SequentIndex,
             rightSubProof: LKProof, aux2: SequentIndex, aux3: SequentIndex,
             mainFormula: FOLFormula ): ForallRightRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( aZero, aX, aSx ) = (
      leftPremise( aux1 ).asInstanceOf[FOLFormula],
      rightPremise( aux2 ).asInstanceOf[FOLFormula], rightPremise( aux3 ).asInstanceOf[FOLFormula] )

    // Find a FOLSubstitution for A[x] and A[0], if possible.
    val sub1 = syntacticMatching( aX, aZero ) match {
      case Some( s ) => s
      case None      => throw LKRuleCreationException( s"Formula $aX can't be matched to formula $aZero." )
    }

    // Find a substitution for A[x] and A[Sx], if possible.
    val sub2 = syntacticMatching( aX, aSx ) match {
      case Some( s ) => s
      case None      => throw LKRuleCreationException( s"Formula $aX can't be matched to formula $aSx." )
    }

    val x = ( sub1.folmap ++ sub2.folmap ).collect { case ( v, e ) if v != e => v }.headOption.getOrElse {
      throw LKRuleCreationException( "Cannot determine induction variable." )
    }

    val baseCase = InductionCase( leftSubProof, FOLConst( "0" ), Seq(), Seq(), aux1 )
    val stepCase = InductionCase( rightSubProof, FOLFunctionConst( "s", 1 ), Seq( aux2 ), Seq( x ), aux3 )

    val All( y, a ) = mainFormula
    ForallRightRule( InductionRule( Seq( baseCase, stepCase ), Abs( y, a ), y ), mainFormula, y )
  }

  /**
   * An LKProof ending with an induction over the natural numbers:
   *
   * <pre>
   *      (π1)                (π2)
   *  Γ :- Δ, A[0]    A[y], Π :- Λ, A[y]
   * ------------------------------------ind
   *           Γ, Π :- Δ, Λ, ∀x. A[x]
   * </pre>
   * Note that there is an eigenvariable condition on x, i.e. x must not occur freely in Π :- Λ.
   *
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The subproof π,,1,,
   * @param aux1 The index of A[0] or the formula itself.
   * @param rightSubProof The subproof π,,2,,
   * @param aux2 The index of A[y] or the formula itself.
   * @param aux3 The index of A[sy] or the formula itself.
   * @param mainFormula The formula ∀x. A[x].
   */
  def apply( leftSubProof: LKProof, aux1: IndexOrFormula,
             rightSubProof: LKProof, aux2: IndexOrFormula, aux3: IndexOrFormula,
             mainFormula: FOLFormula ): ForallRightRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )
    val ( _, leftIndicesSuc ) = findAndValidate( leftPremise )( Seq(), Seq( aux1 ) )
    val ( rightIndicesAnt, rightIndicesSuc ) = findAndValidate( rightPremise )( Seq( aux2 ), Seq( aux3 ) )

    apply( leftSubProof, Suc( leftIndicesSuc( 0 ) ),
      rightSubProof, Ant( rightIndicesAnt( 0 ) ), Suc( rightIndicesSuc( 0 ) ), mainFormula )
  }
}
