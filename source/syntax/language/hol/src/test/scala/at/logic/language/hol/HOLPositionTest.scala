package at.logic.language.hol

import HOLPosition._
import at.logic.language.lambda.types._
import at.logic.language.hol._

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class HOLPositionTest extends SpecificationWithJUnit {
  "HOLPositions" should {
    "be computed correctly" in {
      val x = HOLVar("x", Ti)
      val y = HOLVar("y", Ti)
      val f = HOLConst("f", Ti -> Ti)
      val c = HOLConst("c", Ti)
      val P = HOLConst("P", Ti -> To)
      val Px = Atom(P, List(x))
      val Pfc = Atom(P, List(HOLApp(f, c)))

      getPositions(Px) must beEqualTo(List(HOLPosition(Nil), HOLPosition(1), HOLPosition(2)))
      replace(Px, HOLPosition(2), HOLApp(f,c)) must beEqualTo(Pfc)
    }
  }
}