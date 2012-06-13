/*
 * Tests for the prover9 interface.
**/

package at.logic.provers.vampire

import _root_.at.logic.parsing.language.simple.SimpleFOLParser
import _root_.at.logic.parsing.readers.StringReader
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mock.Mockito
import org.mockito.Matchers._
import java.io.IOException

// to use matchers like anyInt()
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent

@RunWith(classOf[JUnitRunner])
class VampireTest extends SpecificationWithJUnit {
  def parse(str:String) : FOLFormula = (new StringReader(str) with SimpleFOLParser getTerm).asInstanceOf[FOLFormula]

  val box = List()
  def checkForVampireOrSkip = Vampire.refute(box) must not(throwA[VampireException]).orSkip


  "The Vampire interface" should {
    "refute { :- P; P :- }" in {
      //checks, if the execution of vampire works, o.w. skip test
      Vampire.refute(box ) must not(throwA[VampireException]).orSkip

      val p = Atom(new ConstantStringSymbol("P"), Nil)
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

      val i = parse("=(f(a,x),x)")
      val s = parse("=(f(f(f(b,x),y),z), f(f(x,z), f(y,z)))")
      val k = parse("=(f(f(c,x),y), x)")
      val skk_i = parse("=(f(f(f(b,c),c),x), f(a,x))")

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

      val s1 = FSequent(Nil, List(parse("P")))
      val t1 = FSequent(List(parse("Q")),Nil)
      val result : Boolean = Vampire.refute( List(s1,t1) )
      result must beEqualTo( false )
    }
  }

}
