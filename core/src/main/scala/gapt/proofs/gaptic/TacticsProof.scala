package gapt.proofs.gaptic

import gapt.proofs.{ Context, ImmutableContext, MutableContext }

class TacticsProof0( initialContext: ImmutableContext ) {
  protected val mutableContext: MutableContext = initialContext.newMutable
  implicit def ctx: ImmutableContext = mutableContext.ctx
  protected def ctx_=( newContext: ImmutableContext ) = { mutableContext.ctx = newContext }
}

class TacticsProof( initialContext: ImmutableContext = Context.default ) extends TacticsProof0( initialContext ) {
  protected implicit def mutableCtxImplicit: MutableContext = mutableContext

  def main( args: Array[String] ): Unit = ()
}
