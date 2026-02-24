package gapt.utils

import org.specs2.mutable.Specification
import org.specs2.matcher.Matchers._

class AborterTest extends Specification {
  "abortable" in {
    "should abort with abortValue if body calls abortIfNotified" in {
      val gotAborted = abortable(true, true) { aborter ?=>
        aborter.abortIfNotified()
        false
      }
      gotAborted must beTrue
    }

    "should abort otherwise infinite loop" in {
      val startTime = System.currentTimeMillis()
      val gotAborted = abortable(System.currentTimeMillis() - startTime >= 10, true) { aborter ?=>
        while (true) {
          aborter.abortIfNotified()
        }
        false
      }
      gotAborted must beTrue
    }

    "should not abort if body does not call abortIfNotified" in {
      val gotAborted = abortable(true, true) { _ ?=>
        Thread.sleep(10)
        false
      }
      gotAborted must beFalse
    }

    "should not abort if body catches arbitrary exceptions around abortIfNotified" in {
      val gotAborted = abortable(true, true) { aborter ?=>
        try aborter.abortIfNotified()
        catch
          case t: Throwable => {
            // this consumes the special exception thrown by abortIfNotified
            // so the abort will not take place
          }
        false
      }
      gotAborted must beFalse
    }

    "should rethrow body exceptions" in {
      abortable(true, true) { _ ?=>
        throw new Exception("test")
      } must throwAn[Exception]("test")
    }
  }
}
