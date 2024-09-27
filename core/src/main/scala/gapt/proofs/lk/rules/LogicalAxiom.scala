package gapt.proofs.lk.rules

import gapt.expr.formula.Formula
import gapt.proofs.HOLSequent

/**
 * An LKProof consisting of a logical axiom:
 * <pre>
 *    --------ax
 *     A :- A
 * </pre>
 * with A atomic.
 *
 * @param A The atom A.
 */
case class LogicalAxiom(A: Formula) extends InitialSequent {
  override def name: String = "ax"
  override def conclusion: HOLSequent = HOLSequent(Seq(A), Seq(A))
  def mainFormula: Formula = A
}
