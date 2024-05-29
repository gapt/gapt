package gapt.expr.formula.hol

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLVar
import org.specs2.mutable._

class UtilsTest extends Specification {
  "dualize" should {
    "be computed correctly" in {
      val x = FOLVar("x")
      val Px = FOLAtom("P", x)
      val Qx = FOLAtom("Q", x)

      val F = All(x, And(Px, Neg(Qx)))
      val G = Ex(x, Or(Neg(Px), Qx))

      dualize(F) must beEqualTo(G)
    }
  }
}
