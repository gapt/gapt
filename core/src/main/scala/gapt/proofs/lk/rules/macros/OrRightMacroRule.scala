package gapt.proofs.lk.rules.macros

import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Or
import gapt.proofs.IndexOrFormula
import gapt.proofs.IndexOrFormula.IsFormula
import gapt.proofs.SequentConnector
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ConvenienceConstructor
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.WeakeningRightRule

object OrRightMacroRule extends ConvenienceConstructor( "OrRightMacroRule" ) {

  /**
   * This simulates an additive ∨:r-rule: if either aux formula (but not both) is missing, it will be added to the
   * premise by weakening before creating the ∨:r inference.
   *
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param leftDisjunct Index of the left disjunct or the disjunct itself.
   * @param rightDisjunct Index of the right disjunct or the disjunct itself.
   * @return
   */
  def apply( subProof: LKProof, leftDisjunct: IndexOrFormula, rightDisjunct: IndexOrFormula ): OrRightRule =
    withSequentConnector( subProof, leftDisjunct, rightDisjunct )._1

  /**
   * This simulates an additive ∨:r-rule: if either aux formula (but not both) is missing, it will be added to the
   * premise by weakening before creating the ∨:r inference.
   *
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param leftDisjunct Index of the left disjunct or the disjunct itself.
   * @param rightDisjunct Index of the right disjunct or the disjunct itself.
   * @return An LKProof and an SequentConnector connecting its end sequent with the end sequent of subProof.
   */
  def withSequentConnector(
    subProof:      LKProof,
    leftDisjunct:  IndexOrFormula,
    rightDisjunct: IndexOrFormula ): ( OrRightRule, SequentConnector ) = {
    val ( _, _, _, indices ) = findIndicesOrFormulasInPremise( subProof.endSequent )(
      Seq(),
      Seq( leftDisjunct, rightDisjunct ) )

    indices match {
      case -1 +: -1 +: _ => // Neither disjunct has been found. We don't allow this case.
        throw LKRuleCreationException(
          s"Neither $leftDisjunct nor $rightDisjunct has been found in succedent of ${subProof.endSequent}." )

      case -1 +: i +: _ => // The right disjunct has been found at index Suc(i).
        // This match cannot fail: if the index of leftDisjunct is -1, it cannot have been passed as an index.
        val IsFormula( ld ) = leftDisjunct: @unchecked
        val subProof_ = WeakeningRightRule( subProof, ld )
        val oc = subProof_.getSequentConnector
        val proof = OrRightRule( subProof_, subProof_.mainIndices( 0 ), oc.child( Suc( i ) ) )
        ( proof, proof.getSequentConnector * oc )

      case i +: -1 +: _ => // The left conjunct has been found at indext Suc(i).
        // This match cannot fail: if the index of rightDisjunct is -1, it cannot have been passed as an index.
        val IsFormula( rd ) = rightDisjunct: @unchecked
        val subProof_ = WeakeningRightRule( subProof, rd )
        val oc = subProof_.getSequentConnector
        val proof = OrRightRule( subProof_, oc.child( Suc( i ) ), subProof_.mainIndices( 0 ) )
        ( proof, proof.getSequentConnector * oc )

      case _ => // Both disjuncts have been found. Simply construct the inference.
        val proof = OrRightRule( subProof, leftDisjunct, rightDisjunct )
        ( proof, proof.getSequentConnector )
    }
  }

  def apply( subProof: LKProof, disjuncts: Seq[Formula] ): LKProof =
    disjuncts match {
      case Seq()    => WeakeningRightRule( subProof, Bottom() )
      case Seq( _ ) => subProof
      case ds :+ d  => apply( apply( subProof, ds ), Or( ds ), d )
    }
}
