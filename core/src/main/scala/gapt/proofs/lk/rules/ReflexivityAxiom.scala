package gapt.proofs.lk.rules

import gapt.expr.Expr
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.proofs.HOLSequent

/**
 * An LKProof consisting of a reflexivity axiom:
 * <pre>
 *    ------------ax
 *      :- s = s
 * </pre>
 * with s a term.
 *
 * @param s The term s.
 */
case class ReflexivityAxiom( s: Expr ) extends InitialSequent {
  override def name: String = "refl"
  override def conclusion: HOLSequent = HOLSequent( Seq(), Seq( Eq( s, s ) ) )
  def mainFormula: Formula = Eq( s, s )
}
