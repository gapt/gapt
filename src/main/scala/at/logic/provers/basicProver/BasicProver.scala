
package at.logic.provers.basicProver

import at.logic.algorithms.lk.LKProver
import at.logic.provers.Prover
import at.logic.provers.minisat.MiniSATProver
import at.logic.language.hol.HOLFormula
import at.logic.proofs.lk.base.{ FSequent, LKProof }

class BasicProver extends Prover {

  // Uses our propositional prover to get LK proof and 
  // minisat for validity check

  def getLKProof( seq: FSequent ): Option[LKProof] =
    new LKProver( cleanStructuralRules = false ).getLKProof( seq )

  override def isValid( seq: FSequent ): Boolean =
    new MiniSATProver().isValid( seq )

  override def isValid( f: HOLFormula ): Boolean = {
    new MiniSATProver().isValid( f )
  }
}
