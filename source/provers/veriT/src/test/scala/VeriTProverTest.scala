/*
 * Tests for verit's interface.
**/

package at.logic.provers.veriT

import at.logic.language.fol._

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class VeriTProverTest extends SpecificationWithJUnit {

  args(skipAll = !VeriTProver.isInstalled())

  "VeriT" should {
    "prove a v not a" in {
      //skipped("--proof-version in isValid is only supported on Giselle's machine")
      val a = Atom("a", Nil)
      val f = Or(a, Neg(a))

      VeriTProver.isValid(f) must beEqualTo(true)
    }
  }
}
