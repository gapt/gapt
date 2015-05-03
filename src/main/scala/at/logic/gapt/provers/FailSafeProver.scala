package at.logic.gapt.provers

import at.logic.gapt.provers.minisat.MiniSATProver
import at.logic.gapt.provers.sat4j.Sat4jProver

object FailSafeProver {
  val minisatInstalled = ( new MiniSATProver ).isInstalled

  def getProver(): Prover = {
    if ( minisatInstalled ) new MiniSATProver else new Sat4jProver
  }

}