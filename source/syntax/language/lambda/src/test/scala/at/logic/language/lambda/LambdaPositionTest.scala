package at.logic.language.lambda

import types._
import LambdaPosition._

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class LambdaPositionTest extends SpecificationWithJUnit {
  "LambdaPositions" should {
    "be computed correctly" in {
      val x = Var("x", Ti)
      val f  = Const("f", ->(Ti,Ti))
      val fx = App(f, x)
      val exp = Abs(x, fx)

      getPositions(x).head must beEqualTo(LambdaPosition(Nil))
      getPositions(exp) must beEqualTo(List(LambdaPosition(Nil), LambdaPosition(1), LambdaPosition(1,1), LambdaPosition(1,2)))
    }

    "be replaced correctly" in {
      val x = Var("x", Ti)
      val y = Var("y", Ti)
      val f  = Const("f", ->(Ti,Ti))
      val fx = App(f, x)
      val fy = App(f, y)
      val exp = Abs(x, fx)
      val expNew = replace(exp, LambdaPosition(1,2), y)

      expNew(LambdaPosition(1)) must beEqualTo(fy)
    }
  }
}