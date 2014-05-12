/*
 * FOLMatchingAlgorithmTest.scala
 *
 */

package at.logic.algorithms.matching

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.fol._

@RunWith(classOf[JUnitRunner])
class FOLMatchingAlgorithmTest extends SpecificationWithJUnit {
  "FOLMatchingAlgorithm" should {
    val x = FOLVar("x")
    val x1 = FOLVar("x1")
    val x2 = FOLVar("x2")
    val x3 = FOLVar("x3")
    val a = FOLConst("a")
    val b = FOLConst("b")
    val c = FOLConst("c")
    val d = FOLConst("d")

    "match correctly the lambda expressions f(x, x) and f(a,b)" in {
      val term = Function("f", x::x::Nil)
      val posInstance = Function("f", a::b::Nil)
      val sub = FOLMatchingAlgorithm.matchTerm(term, posInstance, freeVariables(posInstance))
      sub must beEqualTo (sub)
    }


    "match correctly the lambda expressions f(x1, x2, c) and f(a,b,c)" in {
      val term = Function("f", x1::x2::c::Nil)
      val posInstance = Function("f", a::b::c::Nil)
      val sub = FOLMatchingAlgorithm.matchTerm(term, posInstance, freeVariables(posInstance))
      sub.get(term) must beEqualTo (posInstance)
    }


    "not match the lambda expressions f(x1, d, c) and f(a,b,c)" in {
      val term = Function("f", x1::d::c::Nil)
      val posInstance = Function("f", a::b::c::Nil)
      val sub = FOLMatchingAlgorithm.matchTerm(term, posInstance, freeVariables(posInstance))
      sub must beEqualTo (None)
    }

    "match the lambda expressions f(x1, x2, c) and f(x1,b,c)" in {
      val term = Function("f", x1::x2::c::Nil)
      val posInstance = Function("f", x1::b::c::Nil)
      val sub = FOLMatchingAlgorithm.matchTerm(term, posInstance, freeVariables(posInstance))
      sub.get(term) must beEqualTo (posInstance)
    }

    "not match the lambda expressions f(x1, x2, c, d) and f(x1,b,c)" in {
      val term = Function("f", x1::x2::c::d::Nil)
      val posInstance = Function("f", x1::b::c::Nil)
      val sub = FOLMatchingAlgorithm.matchTerm(term, posInstance, freeVariables(posInstance))
      sub must beEqualTo (None)
    }

    "match the lambda expressions f(x1, x2, c) and f(x3,b,c)" in {
      val term = Function("f", x1::x2::c::Nil)
      val posInstance = Function("f", x3::b::c::Nil)
      val sub = FOLMatchingAlgorithm.matchTerm(term, posInstance, freeVariables(posInstance))
      sub.get(term) must beEqualTo (posInstance)
    }

    "match the lambda expressions f(x1, x2, x3) and f(x3,b,x3)" in {
      val term = Function("f", x1::x2::x3::Nil)
      val posInstance = Function("f", x3::b::x3::Nil)
      val sub = FOLMatchingAlgorithm.matchTerm(term, posInstance, freeVariables(posInstance))
      sub.get(term) must beEqualTo (posInstance)
    }

    "match the lambda expressions f(x1, x1, x3) and f(x3,b,g(d))" in {
      val term = Function("f", x1::x1::x3::Nil)
      val gd = Function("g", d::Nil)
      val posInstance = Function("f", x3::b::gd::Nil)
      val sub = FOLMatchingAlgorithm.matchTerm(term, posInstance, freeVariables(posInstance))
      sub must beEqualTo (None)
    }

    "match the FOL formulas P(x1,f(x1, g(x1,x3), x3)) and P(c,f(x1, g(x1,a), x3))" in {
      val gx1x3 = Function("g", x1::x3::Nil)
      val gx1a = Function("g", x1::a::Nil)
      val term1 = Function("f", x1::gx1x3::x3::Nil)
      val term2 = Function("f", c::gx1a::x3::Nil)
      val P1 = AllVar(x1, Atom("P", x1::term1::Nil))
      val P2 = AllVar(x1, Atom("P", c::term2::Nil))
      val sub1 = FOLMatchingAlgorithm.matchTerm(P1, P2, freeVariables(P2))
      // ??
      0 must beEqualTo (0)
    }

    "match the FOL formulas And(P(x1,f(x1, g(x1,x3), x3)),Q(x1)) and And(P(c,f(c, g(x1,a), x3)),Q(c))" in {
      val gx1x3 = Function("g", x1::x3::Nil)
      val gx1a = Function("g", x1::a::Nil)
      val term1 = Function("f", x1::gx1x3::x3::Nil)
      val term2 = Function("f", c::gx1a::x3::Nil)
      val P1 = And(Atom("P", x1::term1::Nil), Atom("Q", x1::Nil))
      val P2 = And(Atom("P", c::term2::Nil), Atom("Q", c::Nil))
      val sub1 = FOLMatchingAlgorithm.matchTerm(P1, P2, freeVariables(P2))
      sub1 must beEqualTo (None)
    }

    "match the FOL formulas And(P(x2,f(x2, g(x1,x3), x3)),Q(c)) and And(P(c,f(c, g(x1,a), x1)),Q(c))" in {
      val gx2x3 = Function("g", x2::x3::Nil)
      val gax1 = Function("g", a::x1::Nil)
      val term1 = Function("f", x2::gx2x3::x3::Nil)
      val term2 = Function("f", c::gax1::x1::Nil)
      val P1 = And(Atom("P", term1::Nil), Atom("Q", c::Nil))
      val P2 = And(Atom("P", term2::Nil), Atom("Q", c::Nil))
      val sub1 = FOLMatchingAlgorithm.matchTerm(P1, P2, freeVariables(P2))
      sub1 must beEqualTo (None)
    }
    
    "match the FOL formulas And(P(f(x2, g(x1,x3), x3)),Q(x2)) and And(P(f(c, g(a,x1), x2)),Q(c))" in {
      val gx2x3 = Function("g", x2::x3::Nil)
      val gcx1 = Function("g", c::x1::Nil)
      val term1 = Function("f", x2::gx2x3::x3::Nil)
      val term2 = Function("f", c::gcx1::x2::Nil)
      val P1 = And(Atom("P", term1::Nil), Atom("Q", x2::Nil))
      val P2 = And(Atom("P", term2::Nil), Atom("Q", c::Nil))
      val sub1 = FOLMatchingAlgorithm.matchTerm(P1, P2, freeVariables(P2))
      sub1 must beEqualTo (None)
    }

    "not match the lambda expressions f(x, b) and f(a,b)" in {
      val term = Function("f", x::b::Nil)
      val posInstance = Function("f", a::b::Nil)
      val sub = FOLMatchingAlgorithm.matchTerm(term, posInstance, freeVariables(posInstance))
      sub.get(term) must beEqualTo (posInstance)
    }
  }
}


