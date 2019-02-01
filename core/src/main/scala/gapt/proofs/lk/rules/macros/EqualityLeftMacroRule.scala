package gapt.proofs.lk.rules.macros

import gapt.expr.Abs
import gapt.proofs.Ant
import gapt.proofs.IndexOrFormula
import gapt.proofs.IndexOrFormula.IsFormula
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ConvenienceConstructor
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.WeakeningLeftRule

object EqualityLeftMacroRule extends ConvenienceConstructor( "EqualityLeftMacroRule" ) {

  /**
   * Like EqualityLeftRule, but the equation need not exist in the premise.
   * If it doesn't, it will automatically be added via weakening.
   * Note that the auxiliary formula does have to occur in the premise.
   *
   * @param subProof The subproof.
   * @param equation Index of the equation or the equation itself.
   * @param auxFormula Index of the aux formula or the formula itself.
   * @return
   */
  def apply( subProof: LKProof, equation: IndexOrFormula, auxFormula: IndexOrFormula, con: Abs ): EqualityLeftRule =
    withSequentConnector( subProof, equation, auxFormula, con )._1

  /**
   * Like EqualityLeftRule, but the equation need not exist in the premise. If it doesn't, it will automatically be added via weakening.
   * Note that the auxiliary formula does have to occur in the premise.
   *
   * @param subProof The subproof.
   * @param equation Index of the equation or the equation itself.
   * @param auxFormula Index of the aux formula or the formula itself.
   * @return An LKProof and an SequentConnector connecting its end sequent with the end sequent of subProof.
   */
  def withSequentConnector( subProof: LKProof, equation: IndexOrFormula,
                            auxFormula: IndexOrFormula,
                            con:        Abs ): ( EqualityLeftRule, SequentConnector ) = {
    val ( _, indices, _, _ ) =
      findIndicesOrFormulasInPremise( subProof.endSequent )( Seq( equation, auxFormula ), Seq() )

    ( indices( 0 ), indices( 1 ) ) match {
      case ( _, -1 ) => // The aux formula has not been found.  We don't allow this case.
        throw LKRuleCreationException( s"Aux formula has not been found in succedent of ${subProof.endSequent}." )

      case ( -1, i ) => // Aux formula has been found at index Ant(i).
        val IsFormula( e ) = equation
        // This match cannot fail: if the index of the equation is -1, it cannot have been passed as an index.
        val subProof_ = WeakeningLeftRule( subProof, e )
        val oc = subProof_.getSequentConnector
        val proof = EqualityLeftRule( subProof_, subProof_.mainIndices( 0 ), oc.child( Ant( i ) ), con )
        ( proof, proof.getSequentConnector * oc )

      case ( _, _ ) => // Both equation and aux formula have been found. Simply construct the inference.
        val proof = EqualityLeftRule( subProof, equation, auxFormula, con )
        ( proof, proof.getSequentConnector )
    }
  }
}
