package gapt.proofs.lk.rules

import gapt.proofs.HOLSequent
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof

/**
 * An LKProof deriving a sequent from another sequent:
 * <pre>
 *        (π)
 *      Γ :- Δ
 *    ----------
 *     Γ' :- Δ'
 * </pre>
 */
abstract class UnaryLKProof extends LKProof {
  /**
   * The immediate subproof of the rule.
   *
   * @return
   */
  def subProof: LKProof

  /**
   * The object connecting the lower and upper sequents.auxFormulas
   *
   * @return
   */
  def getSequentConnector: SequentConnector = occConnectors.head

  /**
   * The upper sequent of the rule.
   *
   * @return
   */
  def premise: HOLSequent = subProof.endSequent

  override def immediateSubProofs: Seq[LKProof] = Seq( subProof )
}

object UnaryLKProof {
  def unapply( p: UnaryLKProof ): Option[( HOLSequent, LKProof )] = Some( p.endSequent, p.subProof )
}