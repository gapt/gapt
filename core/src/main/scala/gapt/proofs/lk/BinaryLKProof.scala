package gapt.proofs.lk

import gapt.proofs.HOLSequent
import gapt.proofs.SequentConnector

/**
 * An LKProof deriving a sequent from two other sequents:
 * <pre>
 *     (π1)     (π2)
 *    Γ :- Δ   Γ' :- Δ'
 *   ------------------
 *        Π :- Λ
 * </pre>
 */
abstract class BinaryLKProof extends LKProof {
  /**
   * The immediate left subproof of the rule.
   *
   * @return
   */
  def leftSubProof: LKProof

  /**
   * The immediate right subproof of the rule.
   *
   * @return
   */
  def rightSubProof: LKProof

  /**
   * The object connecting the lower and left upper sequents.
   *
   * @return
   */
  def getLeftSequentConnector: SequentConnector = occConnectors.head

  /**
   * The object connecting the lower and right upper sequents.
   *
   * @return
   */
  def getRightSequentConnector: SequentConnector = occConnectors.tail.head

  /**
   * The left upper sequent of the rule.
   *
   * @return
   */
  def leftPremise: HOLSequent = leftSubProof.endSequent

  /**
   * The right upper sequent of the rule.
   *
   * @return
   */
  def rightPremise: HOLSequent = rightSubProof.endSequent

  override def immediateSubProofs: Seq[LKProof] = Seq( leftSubProof, rightSubProof )
}

object BinaryLKProof {
  def unapply( p: BinaryLKProof ): Option[( HOLSequent, LKProof, LKProof )] =
    Some( p.endSequent, p.leftSubProof, p.rightSubProof )
}