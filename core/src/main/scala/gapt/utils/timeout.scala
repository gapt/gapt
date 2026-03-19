package gapt.utils

import scala.concurrent._
import scala.concurrent.duration._
import java.nio.channels.ClosedByInterruptException

class TimeOutException(cause: Throwable, val duration: Duration)
    extends Exception(s"Timeout of $duration exceeded.", cause)

/**
 * runs f with timeout to
 *
 * If f does terminate within to milliseconds returns its result. If not
 * throw a TimeOutException. If f throws an exception it is propagated to
 * the caller of withTimeout.
 *
 * @example
 * {{{
 * try { withTimeout( 1234 ) {
 *   /* ... your code ... */
 * } } catch {
 *   case e: TimeOutException /* ... */
 *   /* other exceptions */
 * }
 * }}}
 */
object withTimeout {
  val logger = Logger("withTimeout")

  @deprecated("Use Durations as argument", "2015-05-15")
  def apply[T](to: Long)(f: => T): T = apply(to millis)(f)

  def apply[T](duration: Duration)(f: Aborter ?=> T): T =
    if (!duration.isFinite)
      f(using Aborter.never)
    else if (duration == Duration.Zero)
      throw new TimeOutException(null, duration)
    else {
      var result: Either[Throwable, T] = Left(new Exception("thread still running"))
      val t = new Thread {
        override def run(): Unit = {
          result =
            try
              abortable(this.isInterrupted(), Left(TimeOutException(null, duration))) {
                Right(f)
              }
            catch {
              case e: InterruptedException       => Left(TimeOutException(e, duration))
              case e: ClosedByInterruptException => Left(TimeOutException(e, duration))
              case t: Throwable                  => Left(t)
            }
        }
      }

      t.setDaemon(true)
      t.start()
      blocking {
        // wait at least one milliseconds, since join(0) would mean to wait forever
        // and giving a sub millisecond timeout duration, e.g., 1 microsecond
        // would round down to zero. thus we choose the smallest non-zero duration
        // which for the join method is 1 millisecond
        val millis = (duration toMillis).max(1)
        t.join(millis)
      }
      t.interrupt()
      // the following assumes that function f uses the aborter interface
      // to check whether it should abort computation in a somewhat frequent fashion.
      // if f does not do that or does it too infrequently then the following will
      // not terminate or terminate later than the given duration.
      // there is no way to make a thread halt its execution if the thread is
      // not cooperating in this fashion
      blocking { t.join() }

      result match {
        case Left(ex)     => throw ex
        case Right(value) => value
      }
    }
}
