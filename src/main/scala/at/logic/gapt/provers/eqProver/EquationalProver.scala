/*
 * Prover for theories modulo equality.
 *
 */

package at.logic.gapt.provers.eqProver

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.prover9._
import at.logic.gapt.provers.veriT._

class EquationalProver extends Prover {

  // Use prover9 to get LK proof and veriT for validity check.

  override def isValid( s: HOLSequent ): Boolean = {
    val p = new VeriTProver()
    p.isValid( s )
  }

  override def getLKProof( s: HOLSequent ) = {
    val p = new Prover9Prover()
    p.getLKProof( s )
  }
}
