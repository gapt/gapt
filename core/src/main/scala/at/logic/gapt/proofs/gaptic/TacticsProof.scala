package at.logic.gapt.proofs.gaptic

import at.logic.gapt.proofs.{ Context, ImmutableContext, MutableContext }

class TacticsProof0( initialContext: ImmutableContext ) {
  protected implicit val mutableContext: MutableContext = initialContext.newMutable
}

class TacticsProof( initialContext: ImmutableContext = Context.default ) extends TacticsProof0( initialContext ) {
  implicit def ctx: ImmutableContext = mutableContext.ctx
  protected def ctx_=( newContext: ImmutableContext ) = { mutableContext.ctx = newContext }

  def main( args: Array[String] ): Unit = ()
}
