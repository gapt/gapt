package gapt.proofs.context.mutable

import gapt.proofs.context.ImmutableContext

trait ReadOnlyMutableContext {

  def ctx: ImmutableContext

}
