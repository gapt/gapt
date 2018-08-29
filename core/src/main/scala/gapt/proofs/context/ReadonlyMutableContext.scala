package gapt.proofs.context

class ReadonlyMutableContext( ctx: ImmutableContext ) extends MutableContext( ctx ) {
  override def ctx_=( newCtx: ImmutableContext ): Unit = throw new UnsupportedOperationException
}
