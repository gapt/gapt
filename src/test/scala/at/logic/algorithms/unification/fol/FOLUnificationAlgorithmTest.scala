/*
 * FOLUnificationAlgorithmTest.scala
 *
 */

package at.logic.algorithms.unification.fol


import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.algorithms.unification.fol._
import at.logic.language.fol._

@RunWith(classOf[JUnitRunner])
class FOLUnificationAlgorithmTest extends SpecificationWithJUnit {

  "UnificationBasedFOLMatchingAlgorithm" should {
    "match correctly the lambda expressions f(x1, x2, c) and f(a,b,c)" in {
      val x = FOLVar("x")
      val a = FOLConst("a")
      val b = FOLConst("b")
      val term = Function("f", x::x::Nil)
      val posInstance = Function("f", a::b::Nil)

      val sub = FOLUnificationAlgorithm.unify(term,posInstance)
      sub must beEqualTo (Nil)
    }
  }

}
