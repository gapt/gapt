package gapt.utils

import org.specs2.execute.{ Failure, Success }
import org.specs2.mutable.Specification
import org.specs2.matcher.Matchers._

import java.util.concurrent.TimeUnit
import scala.concurrent.duration.Duration
class timeoutTest extends Specification {
  "Running a thread with a timeout" in {
    "should be able to interrupt an infinite loop" in {
      val d = Duration( 10, TimeUnit.MILLISECONDS )
      //val d = Duration.Inf
      withTimeout( d )(
        while ( true ) {
          /* do nothing */
        } ) must throwA[TimeOutException]
    }
  }

}
