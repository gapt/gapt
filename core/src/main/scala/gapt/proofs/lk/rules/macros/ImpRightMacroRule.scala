package gapt.proofs.lk.rules.macros

import gapt.proofs.Ant
import gapt.proofs.IndexOrFormula
import gapt.proofs.IndexOrFormula.IsFormula
import gapt.proofs.SequentConnector
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ConvenienceConstructor
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule

object ImpRightMacroRule extends ConvenienceConstructor( "ImpRightMacroRule" ) {

  /**
   * This simulates an additive →:r-rule: if either aux formula (but not both) is missing, it will be added to the
   * premise by weakening before creating the →:r inference.
   *
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param impPremise Index of the premise or the premise itself.
   * @param impConclusion Index of the conclusion or the conclusion itself.
   * @return
   */
  def apply( subProof: LKProof, impPremise: IndexOrFormula, impConclusion: IndexOrFormula ): ImpRightRule =
    withSequentConnector( subProof, impPremise, impConclusion )._1

  /**
   * This simulates an additive →:r-rule: if either aux formula (but not both) is missing, it will be added to the
   * premise by weakening before creating the →:r inference.
   *
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param impPremise Index of the premise or the premise itself.
   * @param impConclusion Index of the conclusion or the conclusion itself.
   * @return An LKProof and an SequentConnector connecting its end sequent with the end sequent of subProof.
   */
  def withSequentConnector(
    subProof:      LKProof,
    impPremise:    IndexOrFormula,
    impConclusion: IndexOrFormula ): ( ImpRightRule, SequentConnector ) = {
    val ( _, indicesAnt, _, indicesSuc ) = findIndicesOrFormulasInPremise( subProof.endSequent )(
      Seq( impPremise ), Seq( impConclusion ) )

    ( indicesAnt.head, indicesSuc.head ) match {
      case ( -1, -1 ) => // Neither aux formula has been found. We don't allow this case.
        throw LKRuleCreationException(
          s"Neither $impPremise nor $impConclusion has been found in succedent of ${subProof.endSequent}." )

      case ( -1, i ) => // The conclusion has been found at index Suc(i).
        // This match cannot fail: if the index of the premise is -1, it cannot have been passed as an index.
        val IsFormula( ip ) = impPremise
        val subProof_ = WeakeningLeftRule( subProof, ip )
        val oc = subProof_.getSequentConnector
        val proof = ImpRightRule( subProof_, subProof_.mainIndices( 0 ), oc.child( Suc( i ) ) )
        ( proof, proof.getSequentConnector * oc )

      case ( i, -1 ) => // The premise has been found at indext Ant(i).
        // This match cannot fail: if the index of the conclusion is -1, it cannot have been passed as an index.
        val IsFormula( ic ) = impConclusion
        val subProof_ = WeakeningRightRule( subProof, ic )
        val oc = subProof_.getSequentConnector
        val proof = ImpRightRule( subProof_, oc.child( Ant( i ) ), subProof_.mainIndices( 0 ) )
        ( proof, proof.getSequentConnector * oc )

      case _ => // Both aux formulas have been found. Simply construct the inference.
        val proof = ImpRightRule( subProof, impPremise, impConclusion )
        ( proof, proof.getSequentConnector )
    }
  }
}
