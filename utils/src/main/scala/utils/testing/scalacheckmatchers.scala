/** matcher for scalacheck property tests for the specs tests - you can write something like
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

import scala.collection.immutable.Set

import org.specs.matcher._

trait ResultMatcher {
    class PositiveResultMatcher extends Matcher[Test.Result] {
        def apply(r : => Test.Result) : (Boolean,String,String)=
        (r.passed,"ScalaCheck passed!","ScalaCheck failed!")
    }

    val bePassed = new PositiveResultMatcher
}

object ResultMatcher extends ResultMatcher


class TestData(var seed:Int,var desc:String)

trait Description { var testdata : TestData = new TestData(-1,"") }

trait PropMatcher {
    class PositiveResultMatcher extends Matcher[Prop]  {
        def apply(r : => Prop) =
        ({
                def labels(ls: Set[String]) = {
                    if(ls.isEmpty) ""
                    else "> Labels of failing property: " + ls.mkString("\n")
                }

                var res = Test.check(Test.defaultParams,r)
                res.status match {
                    case Test.Proved(args) => println("ok!"); println(args); (true,"OK, proved property.","")
                    case Test.Passed => println("ok!"); (true,"OK, passed "+res.succeeded+" tests.","")
                    case Test.Failed(args, l) =>
                        println("Failed labels:"+labels(l)+" args were "+args)

                        (false,"","Falsified after "+res.succeeded+" passed tests.labels were "+labels(l))
                    case Test.Exhausted =>
                        println("Exhausted the tests!")
                        (false,"","Gave up after only "+res.succeeded+" passed tests. " +
                         res.discarded+" tests were discarded.")
                    case Test.PropException(args,e,l) =>
                        println("Exception:"+ e.getMessage() )
                        (false,"Exception raised on property evaluation." + labels(l) + "> Exception: " + e.getMessage(),"")
                    case Test.GenException(e) =>
                        println("Argument Generation Exception:"+ e.getMessage() )
                        (false,"","Exception raised on argument generation."+"> Stack trace: ")

                    case _ => (false,"","Unknown Scalacheck Result Status!")
                }
            }
        )
    }

    val bePassed = new PositiveResultMatcher
}

object PropMatcher extends PropMatcher
