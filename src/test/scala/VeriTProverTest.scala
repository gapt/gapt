/*
 * Tests for verit's interface.
**/

package at.logic.provers.veriT

import at.logic.proofs.lk.base.FSequent
import at.logic.language.fol._

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class VeriTProverTest extends SpecificationWithJUnit {

  val veriT = new VeriTProver()

  args(skipAll = !veriT.isInstalled())

  "VeriT" should {
    "prove a v not a" in {
      //skipped("--proof-version in isValid is only supported on Giselle's machine")
      val a = FOLAtom("a", Nil)
      val f = FOLOr(a, FOLNeg(a))

      veriT.isValid(f) must beEqualTo(true)
    }

    "parse the proof of a |- a" in {
      val a = FOLAtom("a")
      val s = FSequent(List(a), List(a))

      veriT.getExpansionSequent(s) must not be None
    }
  }
}
