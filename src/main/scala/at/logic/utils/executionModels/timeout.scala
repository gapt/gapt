package at.logic.utils.executionModels

import scala.concurrent._
import scala.concurrent.Await
import scala.concurrent.duration._
import ExecutionContext.Implicits.global

package timeout {

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
  object withTimeout {
    def apply[T]( to: Duration )( f: => T ): T = {
      Await.result( Future { f }, to )
    }
  }

}
