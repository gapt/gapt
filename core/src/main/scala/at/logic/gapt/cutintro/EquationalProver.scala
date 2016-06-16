/*
 * Prover for theories modulo equality.
 *
 */

package at.logic.gapt.cutintro

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9._
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.verit._

/** Use prover9 to get LK proof and Z3 or veriT for validity check. */
object EquationalProver extends Prover {
  private val smtSolver =
    if ( Z3 isInstalled ) Z3
    else if ( VeriT isInstalled ) VeriT
    else new Escargot( splitting = true, equality = true, propositional = true )
  private val resProver =
    if ( Prover9 isInstalled ) Prover9
    else Escargot

  override def startIncrementalSession() = smtSolver.startIncrementalSession()
  override def isValid( s: HOLSequent ): Boolean = smtSolver isValid s
  override def getLKProof( s: HOLSequent ) = resProver getLKProof s
}
