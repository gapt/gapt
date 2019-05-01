package gapt.provers.viper.aip.axioms

import gapt.expr.formula.Formula
import gapt.proofs.lk.LKProof

trait Axiom {
  /**
   * @return The formula representing the axiom.
   */
  def formula: Formula

  /**
   * @return A proof of the axiom.
   */
  def proof: LKProof
}
