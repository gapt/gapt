package at.logic.provers

import at.logic.provers.minisat.MiniSATProver
import at.logic.provers.sat4j.Sat4jProver

object FailSafeProver {
  val minisatInstalled = ( new MiniSATProver ).isInstalled()

  def getProver(): Prover = {
    if ( minisatInstalled ) new MiniSATProver else new Sat4jProver
  }

}