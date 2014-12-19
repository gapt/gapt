/*
 * NaiveIncompleteMatchingAlgorithmTest.scala
 *
 */

package at.logic.algorithms.matching

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.hol._
import at.logic.language.lambda.types._

@RunWith(classOf[JUnitRunner])
class NaiveIncompleteMatchingAlgorithmTest extends SpecificationWithJUnit {
  "NaiveIncompleteMatchingAlgorithm " should {
    "match correctly the HOL expressions P(a,x) and P(a,f(b))" in {
      val P = HOLConst("P", Ti->(Ti->To))
      val a = HOLConst("a", Ti)
      val b = HOLConst("b", Ti)
      val Pa = HOLApp(P,a);
      val x = HOLVar("x", Ti)
      val Pax = HOLApp(Pa,x)
      val f = HOLConst("f", Ti->Ti)
      val fb= HOLApp(f,b)
      val Pafb = HOLApp(Pa,fb)
      val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(Pax,Pafb)
      val subst1 = Substitution(x,fb)
      subst must beEqualTo (Some(subst1))
    }

    "match correctly the HOL expressions P(z,x) and P(f(b),f(b))" in {
      val P = HOLConst("P", Ti->(Ti->To))
      val b = HOLConst("b", Ti)
      val x = HOLVar("x", Ti)
      val z = HOLVar("z", Ti)
      val Pz = HOLApp(P,z)
     
      val Pzx = HOLApp(Pz,x)
      val f = HOLConst("f", Ti->Ti)
      val fb= HOLApp(f,b)
      val Pfb = HOLApp(P,fb)
      val Pfbfb = HOLApp(Pfb,fb)
      val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(Pzx,Pfbfb)
      val subst1 = Substitution(Map((x, fb), (z, fb)))
      subst must beEqualTo (Some(subst1))
    }

    "NOT match correctly the HOL expressions P(z,x) and P(f(b),z)" in {
      val P = HOLConst("P", Ti->(Ti->To))
      val b = HOLConst("b", Ti)
      val x = HOLVar("x", Ti)
      val z = HOLVar("z", Ti)
      val Pz = HOLApp(P,z)
      val Pzx = HOLApp(Pz,x)
      val f = HOLConst("f", Ti->Ti)
      val fb= HOLApp(f,b)
      val Pfb = HOLApp(P,fb)
      val Pfbz = HOLApp(Pfb,z)
      val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(Pzx,Pfbz)
      val subst1 = Substitution( Map((z,fb), (x,z)) )
      subst must beEqualTo (None)         // correct !!!
    }

    "match correctly the HOL expression a < p(x) with itself" in {
      val lt = HOLConst("<", Ti->(Ti->To))
      val a = HOLConst("a", Ti)
      val p = HOLConst("p", Ti->Ti)
      val x = HOLVar("x", Ti)
      val px = Function(p, x::Nil)
      val at = Function(lt, a::px::Nil)
      val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(at, at)
      subst must beEqualTo (Some(Substitution()))
    }

    "match correctly the HOL expression a < p(x) with another copy of itself" in {
      val lt = HOLConst("<", Ti->(Ti->To))
      val a = HOLConst("a", Ti)
      val p = HOLConst("p", Ti->Ti)
      val x = HOLVar("x", Ti)
      val px = Function(p, x::Nil)
      val at = Function(lt, a::px::Nil)
      val at2 = Function(lt, a::px::Nil) // Is this a copy?
      val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(at, at2)
      subst must beEqualTo (Some(Substitution()))
    }
  }
}


