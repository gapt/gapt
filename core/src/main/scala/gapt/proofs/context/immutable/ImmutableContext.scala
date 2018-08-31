package gapt.proofs.context.immutable

import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.context.update.Update

class ImmutableContext private ( val state: State, val updates: List[Update] ) extends Context {
  def toImmutable: ImmutableContext = this

  /**
   * Adds an element to the context.
   *
   * If this is not a valid addition, then an exception is thrown.
   */
  override def +( update: Update ): ImmutableContext =
    new ImmutableContext( update( this ), update :: updates )
}
object ImmutableContext {
  val empty = new ImmutableContext( State(), Nil )
}