package gapt.proofs.lk.rules

import gapt.expr.Const
import gapt.expr.PropFormula
import gapt.expr.Top
import gapt.proofs.HOLSequent

/**
 * An LKProof introducing ⊤ on the right:
 * <pre>
 *       --------⊤:r
 *         :- ⊤
 * </pre>
 */
case object TopAxiom extends InitialSequent {
  override def name: String = "⊤:r"
  override def conclusion: HOLSequent = HOLSequent( Nil, Seq( Top() ) )
  def mainFormula: PropFormula with Const = Top()
}
