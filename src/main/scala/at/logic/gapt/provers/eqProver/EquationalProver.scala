/*
 * Prover for theories modulo equality.
 *
 */

package at.logic.gapt.provers.eqProver

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.prover9._
import at.logic.gapt.provers.veriT._

/** Use prover9 to get LK proof and veriT for validity check. */
object EquationalProver extends Prover {
  override def isValid( s: HOLSequent ): Boolean = VeriT isValid s
  override def getLKProof( s: HOLSequent ) = Prover9 getLKProof s
}
