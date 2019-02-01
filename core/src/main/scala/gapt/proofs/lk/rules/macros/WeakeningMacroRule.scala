package gapt.proofs.lk.rules.macros

import gapt.expr.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ConvenienceConstructor

/**
 * This macro rule simulates a series of weakenings in both cedents.
 *
 */
object WeakeningMacroRule extends ConvenienceConstructor( "WeakeningMacroRule" ) {

  /**
   *
   * @param p A proof.
   * @param antList A list of formulas.
   * @param sucList A list of formulas.
   * @return A new proof whose antecedent and succedent contain new occurrences of the formulas
   *         in antList and sucList, respectively.
   */
  def apply( p: LKProof, antList: Seq[Formula], sucList: Seq[Formula] ): LKProof =
    withSequentConnector( p, antList, sucList )._1

  /**
   *
   * @param p A proof.
   * @param antList A list of formulas.
   * @param sucList A list of formulas.
   * @return A new proof whose antecedent and succedent contain new occurrences of the formulas
   *         in antList and sucList, respectively, and an SequentConnector.
   */
  def withSequentConnector(
    p:       LKProof,
    antList: Seq[Formula], sucList: Seq[Formula] ): ( LKProof, SequentConnector ) = {
    val ( subProof, upperConnector ) = WeakeningLeftMacroRule.withSequentConnector( p, antList )
    val ( proof, lowerConnector ) = WeakeningRightMacroRule.withSequentConnector( subProof, sucList )
    ( proof, lowerConnector * upperConnector )
  }

  /**
   *
   * @param p A proof.
   * @param targetSequent A sequent of formulas.
   * @param strict If true, will require that targetSequent contains the end sequent of p.
   * @return A proof whose end sequent is targetSequent.
   */
  def apply( p: LKProof, targetSequent: HOLSequent, strict: Boolean = true ): LKProof =
    withSequentConnector( p, targetSequent, strict )._1

  /**
   *
   * @param p A proof.
   * @param targetSequent A sequent of formulas.
   * @param strict If true, will require that targetSequent contains the end sequent of p.
   * @return A proof whose end sequent is targetSequent and an SequentConnector.
   */
  def withSequentConnector( p: LKProof, targetSequent: HOLSequent,
                            strict: Boolean = true ): ( LKProof, SequentConnector ) = {
    val currentSequent = p.endSequent

    if ( strict & !( currentSequent isSubMultisetOf targetSequent ) )
      throw LKRuleCreationException( "Sequent " + targetSequent + " cannot be reached from " +
        currentSequent + " by weakenings." )

    val ( antDiff, sucDiff ) = ( targetSequent diff currentSequent ).toTuple

    WeakeningMacroRule.withSequentConnector( p, antDiff, sucDiff )
  }
}
