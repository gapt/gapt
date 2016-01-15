/*
 * Prover for theories modulo equality.
 *
 */

package at.logic.gapt.provers.eqProver

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.{ OneShotProver, Prover }
import at.logic.gapt.provers.prover9._
import at.logic.gapt.provers.veriT._

/** Use prover9 to get LK proof and Z3 or veriT for validity check. */
object EquationalProver extends Prover {
  private val smtSolver = if ( Z3 isInstalled ) Z3 else VeriT

  override def startIncrementalSession() = smtSolver.startIncrementalSession()
  override def isValid( s: HOLSequent ): Boolean = smtSolver isValid s
  override def getLKProof( s: HOLSequent ) = Prover9 getLKProof s
}
