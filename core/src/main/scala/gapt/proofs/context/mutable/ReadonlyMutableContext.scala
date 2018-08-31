package gapt.proofs.context.mutable

import gapt.proofs.context.ImmutableContext

class ReadonlyMutableContext( ctx: ImmutableContext ) extends MutableContext( ctx ) {
  override def ctx_=( newCtx: ImmutableContext ): Unit = throw new UnsupportedOperationException
}
