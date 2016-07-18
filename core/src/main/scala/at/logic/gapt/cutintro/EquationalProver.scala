/*
 * Prover for theories modulo equality.
 *
 */

package at.logic.gapt.cutintro

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lk.EquationalLKProver
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.verit._

/** Use solveQuasiPropositional to get LK proof and Z3/veriT/Escargot for validity check. */
object EquationalProver extends Prover {
  private val smtSolver =
    if ( Z3 isInstalled ) Z3
    else if ( VeriT isInstalled ) VeriT
    else new Escargot( splitting = true, equality = true, propositional = true )

  override def startIncrementalSession() = smtSolver.startIncrementalSession()
  override def isValid( s: HOLSequent ): Boolean = smtSolver isValid s
  override def getLKProof( s: HOLSequent ) = EquationalLKProver getLKProof s
}
