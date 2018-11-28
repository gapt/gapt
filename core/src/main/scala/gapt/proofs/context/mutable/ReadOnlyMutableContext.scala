package gapt.proofs.context.mutable

import gapt.proofs.context.immutable.ImmutableContext

trait ReadOnlyMutableContext {

  def ctx: ImmutableContext

}
