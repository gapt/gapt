/*
 * Prover for theories modulo equality.
 *
 */

package at.logic.gapt.provers.eqProver

import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.prover9._
import at.logic.gapt.provers.veriT._
import at.logic.gapt.language.hol.HOLFormula
import at.logic.gapt.proofs.lk.base.FSequent

class EquationalProver extends Prover {

  // Use prover9 to get LK proof and veriT for validity check.

  override def isValid( s: FSequent ): Boolean = {
    val p = new VeriTProver()
    p.isValid( s )
  }

  override def getLKProof( s: FSequent ) = {
    val p = new Prover9Prover()
    p.getLKProof( s )
  }
}
