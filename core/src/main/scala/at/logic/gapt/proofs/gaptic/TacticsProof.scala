package at.logic.gapt.proofs.gaptic

import at.logic.gapt.proofs.FiniteContext

class TacticsProof {
  private var _ctx = FiniteContext()
  protected def ctx_=( newContext: FiniteContext ) = { _ctx = newContext }
  implicit def ctx = _ctx

  def main( args: Array[String] ): Unit = ()
}
