/*
 * Tests for the prover9 interface.
**/

package at.logic.provers.prover9

import _root_.at.logic.parsing.language.simple.SimpleFOLParser
import _root_.at.logic.parsing.readers.StringReader
import org.specs._
import org.specs.runner._
import org.specs.mock.Mockito
import org.mockito.Matchers._
import java.io.IOException

// to use matchers like anyInt()
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base._

class Prover9Test extends SpecificationWithJUnit {
  def parse(str:String) : FOLFormula = (new StringReader(str) with SimpleFOLParser getTerm).asInstanceOf[FOLFormula]

  val box = List()

  "The Prover9 interface" should {
    "refute { :- P; P :- }" in {
      //checks, if the execution of prover9 works, o.w. skip test
      Prover9.refute(box ) must not(throwA[IOException]).orSkip

      val p = Atom(new ConstantStringSymbol("P"), Nil)
      val s1 = Sequent(Nil, p::Nil)
      val s2 = Sequent(p::Nil, Nil)
      val result : Boolean = Prover9.refute( s1::s2::Nil )
      result must beEqual( true )
    }
  }

  "The Prover9 interface" should {
    "prove SKKx = Ix : { :- f(a,x) = x; :- f(f(f(b,x),y),z) = f(f(x,z), f(y,z)); :- f(f(c,x),y) = x; f(f(f(b,c),c),x) = f(a,x) :- }" in {
      //checks, if the execution of prover9 works, o.w. skip test
      Prover9.refute(box ) must not(throwA[IOException]).orSkip

      val i = parse("=(f(a,x),x)")
      val s = parse("=(f(f(f(b,x),y),z), f(f(x,z), f(y,z)))")
      val k = parse("=(f(f(c,x),y), x)")
      val skk_i = parse("=(f(f(f(b,c),c),x), f(a,x))")

      val s1 = Sequent(Nil, List(i))
      val s2 = Sequent(Nil, List(k))
      val s3 = Sequent(Nil, List(s))
      val t1 = Sequent(List(skk_i),Nil)
      val result : Boolean = Prover9.refute( List(s1,s2,s3,t1) )
      result must beEqual( true )
    }
  }

  "The Prover9 interface" should {
    "not refute { :- P; Q :- }" in {
      //checks, if the execution of prover9 works, o.w. skip test
      Prover9.refute(box ) must not(throwA[IOException]).orSkip

      val s1 = Sequent(Nil, List(parse("P")))
      val t1 = Sequent(List(parse("Q")),Nil)
      val result : Boolean = Prover9.refute( List(s1,t1) )
      result must beEqual( false )
    }
  }

}
