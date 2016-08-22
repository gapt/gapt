package at.logic.gapt.proofs.gaptic

import at.logic.gapt.proofs.Context

class TacticsProof {
  private var _ctx = Context()
  protected def ctx_=( newContext: Context ) = { _ctx = newContext }
  implicit def ctx = _ctx

  def main( args: Array[String] ): Unit = ()
}
