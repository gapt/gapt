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
import at.logic.gapt.utils.Maybe

class ManySortedProver( prover: ResolutionProver ) extends ResolutionProver {
  override def isValid( sequent: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = {
    val reduction = CNFReductionLKRes |> PredicateReductionCNF |> ErasureReductionCNF
    val ( folProblem, _ ) = reduction forward sequent
    prover.getResolutionProof( folProblem )( ctx.map( _.newMutable ) ).isDefined
  }

  override def getExpansionProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
    val reduction = PredicateReductionET |> ErasureReductionET
    val ( folProblem, back ) = reduction forward sequent
    prover.getExpansionProof( folProblem ).map( back )
  }

  override def getLKProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = {
    val reduction = CNFReductionLKRes |> PredicateReductionCNF |> ErasureReductionCNF
    val ( folProblem, back ) = reduction forward sequent
    prover.getResolutionProof( folProblem ).map( proof => back( eliminateSplitting( proof ) ) )
  }

  override def getResolutionProof( seq: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] = {
    val reduction = PredicateReductionCNF |> ErasureReductionCNF
    val ( folProblem, back ) = reduction forward seq.toSet
    prover.getResolutionProof( folProblem ).map( back )
  }
}
