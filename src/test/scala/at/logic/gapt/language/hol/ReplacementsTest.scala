/*
 * ReplacementsTest.scala
 *
 */

package at.logic.gapt.language.hol.replacements

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.gapt.language.hol._
import at.logic.gapt.language.lambda.types._

@RunWith(classOf[JUnitRunner])
class ReplacementsTest extends SpecificationWithJUnit {
  "Replacements" should {
    "work correctly on" in {
      "Atoms" in {
        val a = HOLConst("a", Ti)
        val b = HOLConst("b", Ti)
        val P = HOLConst("P", Ti -> To)
        val atom1 = HOLAtom(P, a::Nil)
        val atom2 = HOLAtom(P, b::Nil)
        val pos = List(1)
        val rep = Replacement(pos, b)
        (rep.apply(atom1)) must beEqualTo (atom2)
      }
    }
  }
}
