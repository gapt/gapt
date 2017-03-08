package at.logic.gapt.provers.viper.aip.axioms

import at.logic.gapt.expr.Formula
import at.logic.gapt.proofs.lk.LKProof

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
