package gapt.proofs.lk

import gapt.expr.Bottom
import gapt.expr.Const
import gapt.expr.PropFormula
import gapt.proofs.HOLSequent

/**
 * An LKProof introducing ⊥ on the left:
 * <pre>
 *       --------⊥:l
 *         ⊥ :-
 * </pre>
 */
case object BottomAxiom extends InitialSequent {
  override def name: String = "⊥:l"
  override def conclusion: HOLSequent = HOLSequent( Seq( Bottom() ), Nil )
  def mainFormula: PropFormula with Const = Bottom()
}
