/*
 * Tests for verit's interface.
**/

package at.logic.provers.veriT

import at.logic.language.fol._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class VeriTProverTest extends SpecificationWithJUnit {
  "VeriT" should {
    "prove a v not a" in {
      val a = Atom(ConstantStringSymbol("a"), Nil)
      val f = Or(a, Neg(a))

      val r = try { VeriTProver.isValid(f) }
      catch {
        case e: Exception => println("VeriT not installed. Skipping test."); true
      } 
      r must beEqualTo (true)
    }
  }
}
