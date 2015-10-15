
package at.logic.gapt.provers.basicProver

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.provers.Prover

class BasicProver extends Prover {

  // Uses our propositional prover to get LK proof and 
  // sat4j for validity check

  def getLKProof( seq: HOLSequent ): Option[LKProof] =
    new LKProver().getLKProof( seq )

  override def isValid( seq: HOLSequent ): Boolean =
    Sat4j.isValid( seq )

  override def isValid( f: HOLFormula ): Boolean =
    Sat4j.isValid( f )
}
