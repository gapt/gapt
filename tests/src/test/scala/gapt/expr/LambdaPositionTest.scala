package gapt.expr

import gapt.expr.ty.Ti
import gapt.expr.util.LambdaPosition
import gapt.expr.util.LambdaPosition._
import org.specs2.mutable._

class LambdaPositionTest extends Specification {
  "LambdaPositions" should {
    "be computed correctly" in {
      val x = Var("x", Ti)
      val f = Const("f", Ti ->: Ti)
      val fx = App(f, x)
      val exp = Abs(x, fx)

      getPositions(x).head must beEqualTo(LambdaPosition(Nil))
      getPositions(exp) must beEqualTo(List(
        LambdaPosition(Nil),
        LambdaPosition(LambdaPosition.Left),
        LambdaPosition(LambdaPosition.Left, LambdaPosition.Left),
        LambdaPosition(LambdaPosition.Left, LambdaPosition.Right)
      ))
    }

    "be replaced correctly" in {
      val x = Var("x", Ti)
      val y = Var("y", Ti)
      val f = Const("f", Ti ->: Ti)
      val fx = App(f, x)
      val fy = App(f, y)
      val exp = Abs(x, fx)
      val expNew = replace(exp, LambdaPosition(Left, Right), y)

      expNew(LambdaPosition(Left)) must beEqualTo(fy)
    }
  }
}
