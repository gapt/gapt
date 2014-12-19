/*
 * Tests for the prover9 interface.
**/

package at.logic.provers.vampire

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol._
import at.logic.calculi.lk.base.FSequent

@RunWith(classOf[JUnitRunner])
class VampireTest extends SpecificationWithJUnit {

  val box = List()
  def checkForVampireOrSkip = Vampire.refute(box) must not(throwA[VampireException]).orSkip

  "The Vampire interface" should {
    "refute { :- P; P :- }" in {
      //checks, if the execution of vampire works, o.w. skip test
      Vampire.refute(box ) must not(throwA[VampireException]).orSkip

      val p = Atom("P", Nil)
      val s1 = FSequent(Nil, p::Nil)
      val s2 = FSequent(p::Nil, Nil)
      val result : Boolean = Vampire.refute( s1::s2::Nil )
      result must beEqualTo( true )
    }
  }

  "The Vampire interface" should {
    "prove SKKx = Ix : { :- f(a,x) = x; :- f(f(f(b,x),y),z) = f(f(x,z), f(y,z)); :- f(f(c,x),y) = x; f(f(f(b,c),c),x) = f(a,x) :- }" in {
      //checks, if the execution of vampire works, o.w. skip test
      Vampire.refute(box ) must not(throwA[VampireException]).orSkip

      val x = FOLVar("x")
      val y = FOLVar("y")
      val z = FOLVar("z")
      val a = FOLConst("a")
      val b = FOLConst("b")
      val c = FOLConst("c")
      val fax = Function("f", a::x::Nil)
      val fbx = Function("f", b::x::Nil)
      val fcx = Function("f", c::x::Nil)
      val fffbxyz = Function("f", Function("f", fbx::y::Nil)::z::Nil)
      val fxz = Function("f", x::z::Nil)
      val fyz = Function("f", y::z::Nil)
      val ffxzfyz = Function("f", fxz::fyz::Nil)
      val ffcxy = Function("f", fcx::y::Nil)
      val fbc = Function("f", b::c::Nil)
      val fffbccx = Function("f", Function("f", fbc::c::Nil)::x::Nil)

      val i = Equation(fax, x)
      val s = Equation(fffbxyz, ffxzfyz)
      val k = Equation(ffcxy, x)
      val skk_i = Equation(fffbccx, fax)

      val s1 = FSequent(Nil, List(i))
      val s2 = FSequent(Nil, List(k))
      val s3 = FSequent(Nil, List(s))
      val t1 = FSequent(List(skk_i),Nil)
      val result : Boolean = Vampire.refute( List(s1,s2,s3,t1) )
      result must beEqualTo( true )
    }
  }

  "The Vampire interface" should {
    "not refute { :- P; Q :- }" in {
      //checks, if the execution of vampire works, o.w. skip test
      Vampire.refute(box ) must not(throwA[VampireException]).orSkip

      val s1 = FSequent(Nil, List(Atom("P", Nil)))
      val t1 = FSequent(List(Atom("Q", Nil)),Nil)
      val result : Boolean = Vampire.refute( List(s1,t1) )
      result must beEqualTo( false )
    }
  }

}
