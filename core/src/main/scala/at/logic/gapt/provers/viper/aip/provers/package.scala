package at.logic.gapt.provers.viper.aip

import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.spass.SPASS
import at.logic.gapt.provers.vampire.Vampire

package object provers {
  object prover9 extends ManySortedProver( Prover9 )

  object eprover extends ManySortedProver( EProver )

  val escargot = Escargot

  object vampire extends ManySortedProver( Vampire )

  object spass extends ManySortedProver( SPASS )

}
