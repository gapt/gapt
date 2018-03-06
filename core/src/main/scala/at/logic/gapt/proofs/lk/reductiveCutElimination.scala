package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.lk.reductions._

/**
 * This object implements a version of Gentzen's cut-elimination
 * proof for our sequent calculus LK. For details, please
 * refer to the documentation of the apply methods.
 */

object cutFree {
  def apply( proof: LKProof ): LKProof =
    ( new UppermostFirstStrategy( nonCommutingCutReduction ) ).run( proof )
}

object isCutFree {
  /**
    * This method checks whether a proof is cut-free.
    * @param proof The proof to check for cut-freeness.
    * @return True if proof does not contain the cut rule, False otherwise.
    */
  def isCutFree( proof: LKProof ): Boolean = proof match {
    case InitialSequent( _ ) => true
    case p: CutRule          => false
    case _                   => proof.immediateSubProofs.forall( isCutFree )
  }
}
