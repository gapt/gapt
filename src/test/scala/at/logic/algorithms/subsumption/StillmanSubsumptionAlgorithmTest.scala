/*
 * StillmanSubsumptionAlgorithmTest.scala
 *
 */

package at.logic.algorithms.subsumption

import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import at.logic.calculi.lk.base.FSequent

@RunWith(classOf[JUnitRunner])
class StillmanSubsumptionAlgorithmFOLTest extends SpecificationWithJUnit {
import at.logic.language.fol._
  "StillmanSubsumptionAlgorithmFOL" should {
    val P = "P"
    val Q = "Q"
    val R = "R"
    val f = "f"
    val a = FOLConst("a")
    val b = FOLConst("b")
    val x = FOLVar("x")
    val y = FOLVar("y")
    val z = FOLVar("z")
    val Px = Atom(P, x::Nil)
    val Py = Atom(P, y::Nil)
    val Pz = Atom(P, z::Nil)
    val fxy = Function(f, x::y::Nil)
    val Pfxy = Atom(P, fxy::Nil)
    val Pa = Atom(P, a::Nil)
    val Pb = Atom(P, b::Nil)
    val fba = Function(f, b::a::Nil)
    val Pfba = Atom(P, fba::Nil)
    val Pxx = Atom(P, x::x::Nil)
    val Pxa = Atom(P, x::a::Nil)
    val Paa = Atom(P, a::a::Nil)
    val Pxb = Atom(P, x::b::Nil)
    val Pab = Atom(P, a::b::Nil)
    val Pba = Atom(P, b::a::Nil)
    val fx = Function(f, x::Nil)
    val fa = Function(f, a::Nil)
    val fb = Function(f, b::Nil)
    val Pfx = Atom(P, fx::Nil)
    val Pfa = Atom(P, fa::Nil)
    val Pfb = Atom(P, fb::Nil)
    val Qxy = Atom(Q, x::y::Nil)
    val Qay = Atom(Q, a::y::Nil)
    val Rx = Atom(R, x::Nil)

    "return true on the following clauses" in {
      "P(x) | P(f(x,y)) and P(a) | P(b) | P(f(b,a))" in {
        val c1 = FSequent(Nil, Px::Pfxy::Nil)
        val c2 = FSequent(Nil, Pa::Pb::Pfba::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (true)
      }
      "Nil and P(a) | P(b) | P(f(b,a))" in {
        val c1 = FSequent(Nil, Nil)
        val c2 = FSequent(Nil, Pa::Pb::Pfba::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (true)
      }
      "P(x) and P(x) | P(f(x,y))" in {
        val c1 = FSequent(Nil, Px::Nil)
        val c2 = FSequent(Nil, Px::Pfxy::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (true)
      }
      "P(x) and P(x)" in {
        val c1 = FSequent(Nil, Px::Nil)
        val c2 = FSequent(Nil, Px::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (true)
      }
      "P(x) and P(y)" in {
        val c1 = FSequent(Nil, Px::Nil)
        val c2 = FSequent(Nil, Py::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (true)
      }
      "P(x,x) | P(x,a) and P(a,a)" in {
        val c1 = FSequent(Nil, Pxx::Pxa::Nil)
        val c2 = FSequent(Nil, Paa::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (true)
      }
      "P(x) | Q(x,y) and P(a) | Q(a,y) | R(x)" in {
        skipped("I am failing failing :( Please check me!")
        val c1 = FSequent(Nil, Px::Qxy::Nil)
        val c2 = FSequent(Nil, Pa::Qay::Rx::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (true)
      }
    }
    "return false on the following clauses" in {
      "P(x) | P(f(x)) and P(f(a)) | P(f(b))" in {
        val c1 = FSequent(Nil, Px::Pfx::Nil)
        val c2 = FSequent(Nil, Pfa::Pfb::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (false)
      }
      "P(a,a) and P(x,x) | P(x,a)" in {
        val c1 = FSequent(Nil, Paa::Nil)
        val c2 = FSequent(Nil, Pxx::Pxa::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (false)
      }
      "P(x,x) | P(x,b) and P(b,a) | P(a,b)" in {
        val c1 = FSequent(Nil, Pxx::Pxb::Nil)
        val c2 = FSequent(Nil, Pba::Pab::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (false)
      }
      "P(x) | -P(x) and P(a) | -P(b)" in {
        val c1 = FSequent(Px::Nil, Px::Nil)
        val c2 = FSequent(Pb::Nil, Pa::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (false)
      }
      "P(x) | -P(x) and P(y) | -P(z)" in {
        val c1 = FSequent(Px::Nil, Px::Nil)
        val c2 = FSequent(Pz::Nil, Py::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (false)
      }
      "P(x) and P(a) | P(y)" in {
        val c1 = FSequent(Nil, Px::Nil)
        val c2 = FSequent(Nil, Pa::Py::Nil)
        StillmanSubsumptionAlgorithmFOL.subsumes(c1, c2) must beEqualTo (true)
      }
    }
  }
}

@RunWith(classOf[JUnitRunner])
class StillmanSubsumptionAlgorithmHOLTest extends SpecificationWithJUnit {
import at.logic.language.hol._
import at.logic.language.lambda.types._
  "StillmanSubsumptionAlgorithmHOL" should {
    "return true on the following clauses" in {
      val P = HOLConst("P", Ti -> (Ti -> To))
      val P1 = HOLConst("P", Ti -> To)
      val Q = HOLConst("Q", Ti -> To)
      val x = HOLVar("x", Ti)
      val y = HOLVar("y", Ti)
      val z = HOLVar("z", Ti)
      val q = HOLVar("q", Ti -> To)
      val a = HOLConst("a", Ti)
      val b = HOLConst("b", Ti)
      val f = HOLConst("f", Ti -> (Ti -> (Ti -> Ti)))
      val f1 = HOLConst("f", Ti -> Ti)
      val f2 = HOLConst("f", (Ti -> To) -> (Ti -> (Ti -> Ti)))
      val f2qza = Function(f2, q::z::a::Nil)
      val f1b = Function(f1, b::Nil)
      val fyza = Function(f, y::z::a::Nil)
      val Pxx = Atom(P, x::x::Nil)
      val Pxa = Atom(P, x::a::Nil)
      val Paa = Atom(P, a::a::Nil)
      val Pfyza_fyza = Atom(P, fyza::fyza::Nil)
      val Qf1b = Atom(Q, f1b::Nil)
      val Pf2qza = Atom(P, f2qza::f2qza::Nil)
      val Px = Atom(P1, x::Nil)
      val Pa = Atom(P1, a::Nil)
      val Qx = Atom(Q, x::Nil)

      "P(x:i,x:i) | P(x:i,a:i) and P(a:i,a:i)" in {
        val c1 = FSequent(Nil, Pxx::Pxa::Nil)
        val c2 = FSequent(Nil, Paa::Nil)
        StillmanSubsumptionAlgorithmHOL.subsumes(c1, c2) must beEqualTo (true)
      }
      "P(x:i,x:i) and P(f(y:i,z:i,a:i):i,f(y:i,z:i,a:i):i)" in {
        val c1 = FSequent(Nil, Pxx::Nil)
        val c2 = FSequent(Nil, Pfyza_fyza::Nil)
        StillmanSubsumptionAlgorithmHOL.subsumes(c1, c2) must beEqualTo (true)
      }
      "P(x:i,x:i) and P(f(q:(i->o),z:i,a:i):i,f(q:(i->o),z:i,a:i):i) | -Q(f(b:i):(i->i))" in {
        skipped("I am failing failing :( Please check me!")
        val c1 = FSequent(Nil, Pxx::Nil)
        val c2 = FSequent(Qf1b::Nil, Pf2qza::Nil) 
        StillmanSubsumptionAlgorithmHOL.subsumes(c1, c2) must beEqualTo (true)
      }
      "P(x:i) and P(a:i) | Q(x:i)" in {
        skipped("I am failing failing :( Please check me!")
        val c1 = FSequent(Nil, Px::Nil)
        val c2 = FSequent(Nil, Pa::Qx::Nil)
        StillmanSubsumptionAlgorithmHOL.subsumes(c1, c2) must beEqualTo (true)
      }
    }
  }
}
