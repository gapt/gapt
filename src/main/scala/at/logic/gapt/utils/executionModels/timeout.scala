package at.logic.gapt.utils.executionModels
import at.logic.gapt.utils.logging.Logger
import scala.concurrent._
import scala.concurrent.duration._

package timeout {

  class TimeOutException( cause: Throwable, val duration: Duration )
    extends Exception( s"Timeout of $duration exceeded.", cause )

  /**
   * runs f with timeout to
   *
   * If f does terminate within to milliseconds returns its result. If not
   * throw a TimeOutException. If f throws an exception it is propagated to
   * the caller of withTimeout.
   *
   * Use this as follows:
   * try { withTimeout( 1234 ) {
   *   ... your code ...
   * } } catch {
   *   case e: TimeOutException ...
   *   case ... other exception
   * }
   */
  object withTimeout extends Logger {
    @deprecated( "Use Durations as argument", "2015-05-15" )
    def apply[T]( to: Long )( f: => T ): T = apply( to millis )( f )

    def apply[T]( duration: Duration )( f: => T ): T = {
      var result: Either[Throwable, T] = Left( new TimeOutException( null, duration ) )

      val t = new Thread {
        override def run() = {
          result = try Right( f ) catch {
            case e: ThreadDeath => Left( new TimeOutException( e, duration ) )
            case t: Throwable   => Left( t )
          }
        }
      }

      t.setDaemon( true )
      t.start()
      blocking { t.join( duration toMillis ) }
      t.stop()

      val nLine = sys.props( "line.separator" )

      // wait until variable result has been written
      t.join( 1.second toMillis )
      if ( t.isAlive ) {
        warn( "Worker thread still alive; stacktrace:" + nLine + t.getStackTrace.mkString( nLine ) )
      }

      result match {
        case Left( t )      => throw t
        case Right( value ) => value
      }
    }
  }

}
