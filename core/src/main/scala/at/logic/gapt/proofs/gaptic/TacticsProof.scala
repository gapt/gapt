package at.logic.gapt.proofs.gaptic

import at.logic.gapt.proofs.Context

class TacticsProof( initialContext: Context = Context.default ) {
  private var _ctx = initialContext
  protected def ctx_=( newContext: Context ) = { _ctx = newContext }
  implicit def ctx = _ctx

  def main( args: Array[String] ): Unit = ()
}
