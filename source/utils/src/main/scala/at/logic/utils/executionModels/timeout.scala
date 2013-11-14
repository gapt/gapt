package at.logic.utils.executionModels

package timeout {

  class TimeOutException extends Exception

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
   **/
  object withTimeout {
    def apply[T]( to: Long )( f: => T ) : T = {
      var result:Either[Throwable,T] = Left(new TimeOutException())

      val r = new Runnable {
        def run() {
          try {
            result = Right( f )
          } catch {
            case e: Exception =>
              result = Left(e)
          }
        }
      }

      val t = new Thread( r )
      t.start()
      t.join( to )
      if ( t.isAlive() ) {
        t.stop()
      }

      if ( result.isLeft ) throw result.left.get
      else result.right.get
    }
  }

}
