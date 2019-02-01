package gapt.proofs.lk.rules.macros

import gapt.proofs.HOLSequent
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ConvenienceConstructor

/**
 * This macro rule simulates a series of contractions in both cedents.
 *
 */
object ContractionMacroRule extends ConvenienceConstructor( "ContractionMacroRule" ) {

  /**
   * Contracts the current proof down to a given sequent.
   *
   * @param p An LKProof.
   * @param targetSequent The target sequent.
   * @param strict If true, the end sequent of p must 1.) contain every formula at least as often as targetSequent
   *               and 2.) contain no formula that isn't contained at least once in targetSequent.
   * @return p with its end sequent contracted down to targetSequent.
   */
  def apply( p: LKProof, targetSequent: HOLSequent, strict: Boolean = true ): LKProof =
    withSequentConnector( p, targetSequent, strict )._1

  /**
   * Contracts the current proof down to a given sequent.
   *
   * @param p An LKProof.
   * @param targetSequent The target sequent.
   * @param strict If true, the end sequent of p must 1.) contain every formula at least as often as targetSequent
   *               and 2.) contain no formula that isn't contained at least once in targetSequent.
   * @return p with its end sequent contracted down to targetSequent and an SequentConnector.
   */
  def withSequentConnector( p: LKProof, targetSequent: HOLSequent,
                            strict: Boolean = true ): ( LKProof, SequentConnector ) = {
    val currentSequent = p.endSequent
    val targetAnt = targetSequent.antecedent
    val targetSuc = targetSequent.succedent

    val assertion = ( ( targetSequent isSubMultisetOf currentSequent )
      && ( currentSequent isSubsetOf targetSequent ) )

    if ( strict & !assertion ) {
      throw LKRuleCreationException(
        s"""Sequent $targetSequent cannot be reached from $currentSequent by contractions.
           |It is missing the following formulas:
           |${( targetSequent diff currentSequent ) ++ ( currentSequent.distinct diff targetSequent.distinct )}
         """.stripMargin )
    }

    val ( subProof, subConnector ) =
      targetAnt.distinct.foldLeft( ( p, SequentConnector( p.endSequent ) ) ) { ( acc, f ) =>
        val n = targetAnt.count( _ == f )
        val ( subProof_, subConnector_ ) = ContractionLeftMacroRule.withSequentConnector( acc._1, f, n )
        ( subProof_, subConnector_ * acc._2 )
      }
    targetSuc.distinct.foldLeft( ( subProof, subConnector ) ) { ( acc, f ) =>
      val n = targetSuc.count( _ == f )
      val ( subProof_, subConnector_ ) = ContractionRightMacroRule.withSequentConnector( acc._1, f, n )
      ( subProof_, subConnector_ * acc._2 )
    }
  }

  /**
   * Performs all possible contractions. Use with care!
   *
   * @param p A proof.
   * @return A proof with all duplicate formulas in the end sequent contracted.
   */
  def apply( p: LKProof ): LKProof = withSequentConnector( p )._1

  /**
   * Performs all possible contractions. Use with care!
   *
   * @param p A proof.
   * @return A proof with all duplicate formulas in the end sequent contracted and an SequentConnector.
   */
  def withSequentConnector( p: LKProof ): ( LKProof, SequentConnector ) = {
    val targetSequent = p.endSequent.distinct
    withSequentConnector( p, targetSequent )
  }

}
