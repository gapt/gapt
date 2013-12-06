/*
 * Prover for theories modulo equality.
 *
 */

package at.logic.provers.eqProver

import at.logic.provers.Prover
import at.logic.provers.prover9._
import at.logic.provers.veriT._
import at.logic.language.hol.HOLFormula
import at.logic.calculi.lk.base.types.FSequent

class EquationalProver extends Prover {

  // Use prover 9 to get lk proof and verit for validity check.

  override def isValid(s: FSequent) : Boolean = VeriTProver.isValid(s) 
  
  override def getLKProof(s: FSequent) = {
    val p = new Prover9Prover()
    p.getLKProof(s) 
  }
}
