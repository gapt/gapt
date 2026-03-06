package gapt.utils

import org.specs2.mutable.Specification
import org.specs2.matcher.Matchers._
import scala.concurrent.duration._

def catCommandExists: Boolean =
  os.exists(os.root / "bin" / "cat")

def devUrandomExists: Boolean =
  os.exists(os.root / "dev" / "urandom")

class timeoutTest extends Specification {
  "Running a thread with a timeout" in {
    "should interrupt an otherwise infinite loop that calls the aborter" in {
      var started = false
      var ended = false
      withTimeout(10 millis) { aborter ?=>
        started = true
        while (true) {
          aborter.abortIfNotified()
        }
        ended = true
      } must throwA[TimeOutException] and
        (started must beTrue) and
        (ended must beFalse)
    }

    "should interrupt a sleeping thread" in {
      var started = false
      var ended = false
      (withTimeout(10 millis) {
        started = true
        Thread.sleep(20)
        ended = true
      } must throwA[TimeOutException]) and
        (started must beTrue) and {
          Thread.sleep(20)
          ended must beFalse
        }
    }

    "should interrupt waiting for external process" in {
      if !catCommandExists then
        skipped("cat command does not exist")
      else if !devUrandomExists then
        skipped("/dev/urandom does not exist")
      else {
        var started = false
        var ended = false
        withTimeout(1000 millis) {
          started = true
          runProcess(Seq("cat", "/dev/urandom"))
          ended = true
        } must throwA[TimeOutException] and
          (started must beTrue) and
          (ended must beFalse)

        success
      }
    }

    "should interrupt a thread joining another thread" in {
      var started = false
      var ended = false
      (withTimeout(10 millis) {
        started = true

        val t = new Thread() {
          override def run(): Unit = {
            while (true) {}
          }
        }
        t.start()
        t.join()

        ended = true
      } must throwA[TimeOutException]) and
        (started must beTrue) and
        (ended must beFalse)
    }

    "should NOT interrupt a loop that does not check for abort" in {
      var started = false
      var ended = false
      withTimeout(10 millis) {
        started = true
        val start = System.currentTimeMillis()
        // run longer than timeout to check that TimeOutException was not triggered
        while (System.currentTimeMillis() - start < 20.milliseconds.toMillis) {}
        ended = true
      } must not(throwAn[Exception]) and
        (started must beTrue) and
        (ended must beTrue)
    }

    "if interrupted on sub millisecond timeouts then actual time passed is more than 1 millisecond" in {
      var started = false
      var ended = false
      val start = System.nanoTime()
      try {
        withTimeout(10.micros) { aborter ?=>
          started = true
          val start = System.nanoTime()
          // run longer than timeout to check that TimeOutException was not
          // triggered, but shorter than 1 millisecond
          while (System.nanoTime() - start < 100.microseconds.toNanos) {}

          // should NOT throw an exception as Thread should not be interrupted
          // within 100 microseconds yet but OS scheduling might affect this
          aborter.abortIfNotified();
          ended = true
        }
        (started must beTrue) and (ended must beTrue)
      } catch {
        case e: TimeOutException =>
          val delta = System.nanoTime() - start
          // we make sure that the TimeOutException was not triggered before
          // one millisecond has passed
          (delta must beGreaterThanOrEqualTo(1.milliseconds.toNanos)) and
            (started must beTrue) and
            (ended must beFalse)
      }
    }

    "should interrupt on sub millisecond timeouts after about 1 millisecond" in {
      var started = false
      var ended = false
      val start = System.nanoTime();
      try {
        withTimeout(10.micros) { aborter ?=>
          started = true
          val start = System.nanoTime()
          // run for 1 millisecond
          while (System.nanoTime() - start < 1.milliseconds.toNanos) {}

          // should throw an exception as Thread should have been interrupted now
          // however this is not completely in our control as os threads might
          // not be interrupted at exactly the time when interrupt is called
          aborter.abortIfNotified();
          ended = true
        }

        val delta = System.nanoTime() - start
        (delta must beGreaterThanOrEqualTo(1.milliseconds.toNanos)) and
          (started must beTrue) and
          (ended must beTrue)
      } catch {
        case e: TimeOutException => {
          val delta = System.nanoTime() - start
          (delta must beGreaterThanOrEqualTo(1.milliseconds.toNanos)) and
            (started must beTrue) and
            (ended must beFalse)
        }
      }
    }

    "should throw immediately on zero timeout and not run body" in {
      var started = false
      withTimeout(0.seconds) {
        started = true
      } must throwA[TimeOutException] and
        (started must beFalse)
    }
  }
}
