package gapt.proofs.lk.rules

import gapt.expr.Const
import gapt.expr.formula.Bottom
import gapt.expr.formula.PropFormula
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
