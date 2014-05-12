/** matcher for scalacheck property tests for the specs tests - you can write something like
 import at.logic.utils.testing.PropMatcher._

 "xyz" should {
 "pass test x" in {
 var prop = //define property
 prop must bePassed
 }

 also take look at http://www.scalatest.org/scaladoc/1.7.2/#org.scalatest.matchers.BeMatcher

 */
package at.logic.utils.testing

import org.specs2.mutable._
////import org.specs.runner._
import org.scalacheck._
import org.scalacheck.Prop._

import org.specs2.matcher._
//import org.scalatest.matchers.{ MatchResult, Matcher }

trait ResultMatcher {
    //def be = new NeutralMatcher[Any]
    class PositiveResultMatcher extends Matcher[Test.Result] {
        def apply[S <: Test.Result](r: Expectable[S]) = Matcher.result(r.value.passed,"ScalaCheck passed!", "ScalaCheck failed!", r)
    }

    val bePassed = new PositiveResultMatcher
}

object ResultMatcher extends ResultMatcher


class TestData(var seed:Int,var desc:String)

trait Description { var testdata : TestData = new TestData(-1,"") }

trait PropMatcher {
    class PositiveResultMatcher extends Matcher[Prop]  {
        def apply[S <: Prop](r: Expectable[S]) =
        ({
                def labels(ls: Set[String]) = {
                    if(ls.isEmpty) ""
                    else "> Labels of failing property: " + ls.mkString("\n")
                }

                var res = Test.check(Test.Params() ,r.value)
                res.status match {
                    case Test.Proved(args) => /* println("ok!"); println(args); */ Matcher.result(true,"OK, proved property.","",r)
                    case Test.Passed => /*println("ok!");*/ Matcher.result(true,"OK, passed "+res.succeeded+" tests.","",r)
                    case Test.Failed(args, l) =>
                        println("Failed labels:"+labels(l)+" args were "+args)

                        Matcher.result(false,"","Falsified after "+res.succeeded+" passed tests.labels were "+labels(l),r)
                    case Test.Exhausted =>
                        println("Exhausted the tests!")
                        Matcher.result(false,"","Gave up after only "+res.succeeded+" passed tests. " +
                         res.discarded+" tests were discarded.",r)
                    case Test.PropException(args,e,l) =>
                        println("Exception:"+ e.getMessage() )
                        Matcher.result(false,"Exception raised on property evaluation." + labels(l) + "> Exception: " + e.getMessage(),"",r)
                    case Test.GenException(e) =>
                        println("Argument Generation Exception:"+ e.getMessage() )
                        Matcher.result(false,"","Exception raised on argument generation."+"> Stack trace: ",r)

                    case _ => Matcher.result(false,"","Unknown Scalacheck Result Status!",r)
                }
            }
        )
    }

    val bePassed = new PositiveResultMatcher
}

object PropMatcher extends PropMatcher
