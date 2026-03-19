package gapt.utils

import scala.util.boundary

// A trait that abstracts over different abort conditions and how to abort.
trait Aborter {
  // The abort condition on which to break
  protected def gotAborted: Boolean

  // The mechanism by which the abort happens. Most likely this will throw an
  // exception that is caught by a special outside context
  protected def break: Unit

  // Signals to the Aborter that the caller can be aborted at this point.
  // It is the caller's responsibility to call this periodically so that the
  // abort can happen as soon as the abort condition is fulfilled.
  // However, it also gives some leeway to the aborter on when to abort to
  // possibly perform cleanup, if necessary.
  def abortIfNotified(): Unit = if gotAborted then break
}

private object NeverAbortSignal extends Aborter {
  override def gotAborted: Boolean = false
  override def break: Unit = ()
}

object Aborter {
  // An aborter that never aborts
  def never: Aborter = NeverAbortSignal

  // the default aborter should be the aborter that never aborts to be compatible
  // with the behaviour before the introduction of the Aborter concept
  given Aborter = Aborter.never
}

// Runs a function inside an Aborter context that aborts when a given abortCondition is fulfilled.
// In that case the abortValue is returned, otherwise the return value of the body is returned.
// The body function should periodically call abortIfNotified on the aborter to signal that the function
// can abort at that point.
//
// A good place to call abortIfNotified is inside a loop that might otherwise not terminate,
// e.g. a saturation loop of a resolution prover.
//
// This is implemented using non-local returns using scala.util.boundary, i.e.,
// throwing a special exception. This means the call to abortIfNotified inside
// body should not be surrounded by a try/catch that will catch arbitrary
// exceptions without rethrowing the exception, otherwise the Aborter context
// will not be able to perform the abort.
def abortable[T](abortCondition: => Boolean, abortValue: T)(body: Aborter ?=> T): T = {
  boundary:
    body(using
      new Aborter {
        protected def gotAborted: Boolean = abortCondition
        protected def break: Unit = boundary.break(abortValue)
      }
    )
}
