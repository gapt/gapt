package gapt.proofs.lk.rules.macros

import gapt.proofs.Ant
import gapt.proofs.IndexOrFormula
import gapt.proofs.IndexOrFormula.IsFormula
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.ConvenienceConstructor
import gapt.proofs.lk.rules.WeakeningLeftRule

object AndLeftMacroRule extends ConvenienceConstructor( "AndLeftMacroRule" ) {

  /**
   * This simulates an additive ∧:l-rule: if either aux formula (but not both) is missing, it will be added to the
   * premise by weakening before creating the ∧:l inference.
   *
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param leftConjunct Index of the left conjunct or the conjunct itself.
   * @param rightConjunct Index of the right conjunct or the conjunct itself.
   * @return
   */
  def apply( subProof: LKProof, leftConjunct: IndexOrFormula, rightConjunct: IndexOrFormula ): AndLeftRule =
    withSequentConnector( subProof, leftConjunct, rightConjunct )._1

  /**
   * This simulates an additive ∧:l-rule: if either aux formula (but not both) is missing, it will be added to the
   * premise by weakening before creating the ∧:l inference.
   *
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param leftConjunct Index of the left conjunct or the conjunct itself.
   * @param rightConjunct Index of the right conjunct or the conjunct itself.
   * @return An LKProof and an SequentConnector connecting its end sequent with the end sequent of subProof.
   */
  def withSequentConnector(
    subProof:      LKProof,
    leftConjunct:  IndexOrFormula,
    rightConjunct: IndexOrFormula ): ( AndLeftRule, SequentConnector ) = {
    val ( _, indices, _, _ ) = findIndicesOrFormulasInPremise( subProof.endSequent )(
      Seq( leftConjunct, rightConjunct ), Seq() )

    indices match {
      case -1 +: -1 +: _ => // Neither conjunct has been found. We don't allow this case.
        throw LKRuleCreationException(
          s"Neither $leftConjunct nor $rightConjunct has been found in antecedent of ${subProof.endSequent}." )

      case -1 +: i +: _ => // The right conjunct has been found at index Ant(i).
        // This match cannot fail: if the index of leftConjunct is -1, it cannot have been passed as an index.
        val IsFormula( lc ) = leftConjunct: @unchecked
        val subProof_ = WeakeningLeftRule( subProof, lc )
        val oc = subProof_.getSequentConnector
        val proof = AndLeftRule( subProof_, Ant( 0 ), oc.child( Ant( i ) ) )
        ( proof, proof.getSequentConnector * oc )

      case i +: -1 +: _ => // The left conjunct has been found at index Ant(i).
        // This match cannot fail: if the index of rightConjunct is -1, it cannot have been passed as an index.
        val IsFormula( rc ) = rightConjunct: @unchecked
        val subProof_ = WeakeningLeftRule( subProof, rc )
        val oc = subProof_.getSequentConnector
        val proof = AndLeftRule( subProof_, oc.child( Ant( i ) ), Ant( 0 ) )
        ( proof, proof.getSequentConnector * oc )

      case _ => // Both conjuncts have been found. Simply construct the inference.
        val proof = AndLeftRule( subProof, leftConjunct, rightConjunct )
        ( proof, proof.getSequentConnector )
    }
  }
}
