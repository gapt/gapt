/*
 * Tests for the prover9 interface.
**/

package at.logic.provers.prover9

import org.specs._
import org.specs.runner._
import org.specs.mock.Mockito
import org.mockito.Matchers._  // to use matchers like anyInt()
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base._

class Prover9Test extends SpecificationWithJUnit {
  "The Prover9 interface" should {
    "refute { :- P; P :- }" in {
      val p = Atom(new ConstantStringSymbol("P"), Nil)
      val s1 = Sequent(Nil, p::Nil)
      val s2 = Sequent(p::Nil, Nil)
      Prover9.refute( s1::s2::Nil ) must beEqual( true )
    }
  }
}
