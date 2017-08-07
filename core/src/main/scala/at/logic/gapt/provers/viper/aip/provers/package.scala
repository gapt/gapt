package at.logic.gapt.provers.viper.aip

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansion.ExpansionProof
import at.logic.gapt.proofs.reduction.ErasureReductionET
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.iprover.IProver
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.spass.SPASS
import at.logic.gapt.provers.vampire.Vampire

package object provers {
  object prover9 extends ManySortedProver( Prover9 )

  object eprover extends ManySortedProver( EProver )

  val escargot = Escargot

  object vampire extends ManySortedProver( Vampire )

  object spass extends ManySortedProver( SPASS )

  object iprover extends ManySortedProver( IProver ) {
    override def getExpansionProof( sequent: HOLSequent ): Option[ExpansionProof] = {
      val reduction = ErasureReductionET
      val ( folProblem, back ) = reduction forward sequent
      IProver.getExpansionProof( folProblem ).map( back )
    }
  }

}
