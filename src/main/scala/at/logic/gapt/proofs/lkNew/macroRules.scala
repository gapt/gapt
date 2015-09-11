package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate

object AndLeftMacroRule extends RuleConvenienceObject( "AndLeftMacroRule" ) {
  def apply( subProof: LKProof, leftConjunct: HOLFormula, rightConjunct: HOLFormula ): LKProof = {
    val ( indices, _ ) = findFormulasInPremise( subProof.endSequent )( Seq( leftConjunct, rightConjunct ), Seq() )
    indices match {
      case -1 +: -1 +: _ => throw LKRuleCreationException( s"Neither $leftConjunct nor $rightConjunct has been found in antecedent of ${subProof.endSequent}." )

      case -1 +: _ +: _ => // The right conjunct has been found.
        AndLeftRule( WeakeningLeftRule( subProof, leftConjunct ), leftConjunct, rightConjunct )

      case _ +: -1 +: _ => // The left conjunct has been found.
        AndLeftRule( WeakeningLeftRule( subProof, rightConjunct ), leftConjunct, rightConjunct )

      case _ => AndLeftRule( subProof, leftConjunct, rightConjunct )
    }
  }
}

object OrRightMacroRule extends RuleConvenienceObject( "OrRightMacroRule" ) {
  def apply( subProof: LKProof, leftDisjunct: HOLFormula, rightDisjunct: HOLFormula ): LKProof = {
    val ( indices, _ ) = findFormulasInPremise( subProof.endSequent )( Seq(), Seq( leftDisjunct, rightDisjunct ) )
    indices match {
      case -1 +: -1 +: _ => throw LKRuleCreationException( s"Neither $leftDisjunct nor $rightDisjunct has been found in succedent of ${subProof.endSequent}." )

      case -1 +: _ +: _ => // The right disjunct has been found.
        OrRightRule( WeakeningRightRule( subProof, leftDisjunct ), leftDisjunct, rightDisjunct )

      case _ +: -1 +: _ => // The left conjunct has been found.
        OrRightRule( WeakeningRightRule( subProof, rightDisjunct ), leftDisjunct, rightDisjunct )

      case _ => OrRightRule( subProof, leftDisjunct, rightDisjunct )
    }
  }
}

object TransRule {
  /**
   * <pre>Performs a proof employing transitivity.
   *
   * Takes a proof π with end-sequent of the form
   * (x=z), Trans, ... |- ...
   * and return one with end-sequent of the form
   * (x=y), (y=z), Trans, ... |- ...
   * where Trans is defined as Forall xyz.((x=y ∧ y=z) -> x=z)
   * </pre>
   * @param x X
   * @param y Y
   * @param z Z
   * @param subProof The proof π which contains the (x=z) which is to be shown.
   * @return A proof with π as a subtree and the formula (x=z) replaced by (x=y) and (y=z).
   */
  def apply( x: FOLTerm, y: FOLTerm, z: FOLTerm, subProof: LKProof ): LKProof = {

    val xv = FOLVar( "x" )
    val yv = FOLVar( "y" )
    val zv = FOLVar( "z" )

    //Forall xyz.(x = y ^ y = z -> x = z)
    val Trans = All( xv, All( yv, All( zv, Imp( And( Eq( xv, yv ), Eq( yv, zv ) ), Eq( xv, zv ) ) ) ) )
    def TransX( x: FOLTerm ) = All( yv, All( zv, Imp( And( Eq( x, yv ), Eq( yv, zv ) ), Eq( x, zv ) ) ) )
    def TransXY( x: FOLTerm, y: FOLTerm ) = All( zv, Imp( And( Eq( x, y ), Eq( y, zv ) ), Eq( x, zv ) ) )
    def TransXYZ( x: FOLTerm, y: FOLTerm, z: FOLTerm ) = Imp( And( Eq( x, y ), Eq( y, z ) ), Eq( x, z ) )

    val xy = Eq( x, y )
    val yz = Eq( y, z )
    val xz = Eq( x, z )

    val ax_xy = LogicalAxiom( xy )
    val ax_yz = LogicalAxiom( yz )

    val s1 = AndRightRule( ax_xy, xy, ax_yz, yz )

    val imp = ImpLeftRule( s1, And( xy, yz ), subProof, xz )

    val allQZ = ForallLeftRule( imp, TransXY( x, y ), z )
    val allQYZ = ForallLeftRule( allQZ, TransX( x ), y )
    val allQXYZ = ForallLeftRule( allQYZ, Trans, x )

    ContractionLeftRule( allQXYZ, Trans )
  }
}

object ForallLeftBlock {
  /**
   * Applies the ForallLeft-rule n times.
   * This method expects a formula main with
   * a quantifier block, and a proof s1 which has a fully
   * instantiated version of main on the left side of its
   * bottommost sequent.
   *
   * The rule:
   * <pre>
   *                (π)
   *  A[x1\term1,...,xN\termN], Γ :- Δ
   * ---------------------------------- (∀_l x n)
   *       ∀ x1,..,xN.A, Γ :- Δ
   * </pre>
   *
   * @param subProof The top proof with (sL, A[x1\term1,...,xN\termN] :- sR) as the bottommost sequent.
   * @param main A formula of the form (Forall x1,...,xN.A).
   * @param terms The list of terms with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * A[x1\term1,...,xN\termN] indeed occurs at the bottom of the proof π.
   */
  def apply( subProof: LKProof, main: HOLFormula, terms: Seq[LambdaExpression] ): LKProof = {
    val partiallyInstantiatedMains = ( 0 to terms.length ).toList.reverse.map( n => instantiate( main, terms.take( n ) ) )

    val series = terms.reverse.foldLeft( ( subProof, partiallyInstantiatedMains ) ) { ( acc, ai ) =>

      ( ForallLeftRule( acc._1, acc._2.tail.head, ai ), acc._2.tail )
    }

    series._1
  }
}

object ForallRightBlock {
  /**
   * Applies the ForallRight-rule n times.
   * This method expects a formula main with
   * a quantifier block, and a proof s1 which has a fully
   * instantiated version of main on the right side of its
   * bottommost sequent.
   *
   * The rule:
   * <pre>
   *              (π)
   *    Γ :- Δ, A[x1\y1,...,xN\yN]
   * ---------------------------------- (∀_r x n)
   *     Γ :- Δ, ∀x1,..,xN.A
   *
   * where y1,...,yN are eigenvariables.
   * </pre>
   *
   * @param subProof The proof π with (sL :- sR, A[x1\y1,...,xN\yN]) as the bottommost sequent.
   * @param main A formula of the form (∀ x1,...,xN.A).
   * @param eigenvariables The list of eigenvariables with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * A[x1\y1,...,xN\yN] indeed occurs at the bottom of the proof π.
   */
  def apply( subProof: LKProof, main: HOLFormula, eigenvariables: Seq[Var] ): LKProof = {
    val partiallyInstantiatedMains = ( 0 to eigenvariables.length ).toList.reverse.map( n => instantiate( main, eigenvariables.take( n ) ) )

    val series = eigenvariables.reverse.foldLeft( ( subProof, partiallyInstantiatedMains ) ) { ( acc, ai ) =>
      ( ForallRightRule( acc._1, acc._2.tail.head, ai ), acc._2.tail )
    }

    series._1
  }
}

/**
 * This macro rule simulates a series of weakenings in the antecedent.
 *
 */
object WeakeningLeftMacroRule {

  /**
   *
   * @param subProof A Proof.
   * @param formulas A list of Formulas.
   * @return A new proof whose antecedent contains new occurrences of the formulas in list.
   */
  def apply( subProof: LKProof, formulas: Seq[HOLFormula] ): LKProof =
    formulas.foldLeft( subProof ) { ( acc, x ) => WeakeningLeftRule( acc, x ) }

  /**
   *
   * @param s1 An LKProof.
   * @param form A Formula.
   * @param n A natural number.
   * @return s1 extended with weakenings such that form occurs at least n times in the antecedent of the end sequent.
   */
  def apply( s1: LKProof, form: HOLFormula, n: Int ): LKProof = {
    val nCurrent = s1.endSequent.antecedent.count( _ == form )

    WeakeningLeftMacroRule( s1, Seq.fill( n - nCurrent )( form ) )
  }
}

