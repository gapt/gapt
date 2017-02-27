package at.logic.gapt.provers.viper.aip.provers

import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion.ExpansionProof
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.proofs.resolution.{ ResolutionProof, eliminateSplitting }
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.spass.SPASS
import at.logic.gapt.provers.vampire.Vampire

object prover9 extends ManySortedProver( Prover9 )

object eprover extends ManySortedProver( EProver )

object escargot extends InternalProver( Escargot )

object vampire extends ManySortedProver( Vampire )

object spass extends ManySortedProver( SPASS )

class InternalProver( prover: ResolutionProver ) {
  /**
   * Checks a sequent for validity.
   *
   * @param sequent The sequent to check for validity.
   * @return true if the sequent is valid, else false or the method does not terminate.
   */
  def isValid( sequent: HOLSequent ): Boolean = prover.isValid( sequent )

  /**
   * Tries to compute a resolution proof for a sequent.
   *
   * @param sequent The sequent to prove.
   * @return A resolution proof if the sequent is provable, otherwise None or the method does not terminate.
   */
  def resolutionProof( sequent: HOLSequent ): Option[ResolutionProof] = prover.getResolutionProof( sequent )

  /**
   * Tries to compute an expansion proof for a sequent.
   *
   * @param sequent The sequent to prove.
   * @return An expansion proof if the sequent is provable, otherwise None or the method does not terminate.
   */
  def expansionProof( sequent: HOLSequent ): Option[ExpansionProof] = prover.getExpansionProof( sequent )

  /**
   * Tries to compute a LK proof for a sequent.
   *
   * @param sequent The sequent to prove.
   * @return A LK proof if the sequent is provable, otherwise None or the method does not terminate.
   */
  def lkProof( sequent: HOLSequent ): Option[LKProof] = prover.getLKProof( sequent )
}

class ManySortedProver( prover: ResolutionProver ) extends InternalProver( prover ) {
  override def isValid( sequent: HOLSequent ): Boolean = {
    val reduction = CNFReductionLKRes |> PredicateReductionCNF |> ErasureReductionCNF
    val ( folProblem, _ ) = reduction forward sequent
    prover.getResolutionProof( folProblem ).isDefined
  }

  override def expansionProof( sequent: HOLSequent ): Option[ExpansionProof] = {
    val reduction = PredicateReductionET |> ErasureReductionET
    val ( folProblem, back ) = reduction forward sequent
    prover.getExpansionProof( folProblem ).map( back )
  }

  override def resolutionProof( sequent: HOLSequent ): Option[ResolutionProof] = {
    val reduction = CNFReductionResRes |> PredicateReductionCNF |> ErasureReductionCNF
    val ( folProblem, back ) = reduction forward sequent
    prover.getResolutionProof( folProblem ).map( back )
  }

  override def lkProof( sequent: HOLSequent ): Option[LKProof] = {
    val reduction = CNFReductionLKRes |> PredicateReductionCNF |> ErasureReductionCNF
    val ( folProblem, back ) = reduction forward sequent
    prover.getResolutionProof( folProblem ).map( proof => back( eliminateSplitting( proof ) ) )
  }
}