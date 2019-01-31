package gapt.proofs.lk

import gapt.proofs.HOLSequent
import gapt.proofs.SequentIndex

/**
 * An LKProof consisting of a single sequent:
 * <pre>
 *     --------ax
 *      Γ :- Δ
 * </pre>
 */
abstract class InitialSequent extends LKProof {

  override def mainIndices: Vector[SequentIndex] = endSequent.indices

  override def auxIndices: Seq[Nothing] = Seq()

  override def immediateSubProofs: Seq[Nothing] = Seq()

  override def occConnectors: Seq[Nothing] = Seq()
}

object InitialSequent {
  def unapply( proof: InitialSequent ): Option[HOLSequent] = Some( proof.endSequent )
}