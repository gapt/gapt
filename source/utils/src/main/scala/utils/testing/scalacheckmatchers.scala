/* matcher for scalacheck property tests for the specs tests - you can write something like
   import at.logic.utils.testing.PropMatcher._

   "xyz" should {
    "pass test x" in {
        var prop = //define property
        prop must bePassed
    }

    also take look at http://www.scalatest.org/scaladoc/doc-1.0/org/scalatest/matchers/BeMatcher.html
 */
package at.logic.utils.testing

import org.specs._
import org.specs.runner._
import org.scalacheck._
import org.scalacheck.Prop._

import org.specs.matcher._

trait ResultMatcher {
        class PositiveResultMatcher extends Matcher[Test.Result] {
            def apply(r : => Test.Result) : (Boolean,String,String)=
                (r.passed,"ScalaCheck passed!","ScalaCheck failed!")
        }

        val bePassed = new PositiveResultMatcher
}

object ResultMatcher extends ResultMatcher

trait PropMatcher {
        class PositiveResultMatcher extends Matcher[Prop] {
            def apply(r : => Prop) =
                (Test.check(Test.defaultParams,r).passed,
                 "ScalaCheck passed!",
                 "ScalaCheck failed!")
        }

        val bePassed = new PositiveResultMatcher
}

object PropMatcher extends PropMatcher
