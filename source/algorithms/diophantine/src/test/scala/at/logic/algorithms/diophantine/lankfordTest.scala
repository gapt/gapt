package at.logic.algorithms.diophantine

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class LankfordSolverTest extends SpecificationWithJUnit {
  "The Lankford Diophantine solver" should {
    "handle vectors correctly" in {
      val v1: Vector = Vector(-1, 0, 1, 0, 0, 2)
      val v2: Vector = Vector(1, 1, 1, 2, 1, 0)
      val v3: Vector = Vector(0, 0, 0, 0, 0, 0)
      val v4: Vector = Vector(0, 1, 2, 2, 1, 2)
      val v5: Vector = Vector(0, 0, 0, 0, 0, 1)
      val v6: Vector = Vector(0, 0, 0, 0, 1, 0)

      //        println (v1-v1)
      //        println (v1+v2)
      //        println (v1+v3)
      //        println (v1-v3)

      (v1 - v1) must beEqualTo(v3)
      (v1 + v2) must beEqualTo(v4)
      (v1 + v3) must beEqualTo(v1)
      (v1 - v3) must beEqualTo(v1)
    }

    "new solve the equation x_1 + x_2 = y_1 + y_2" in {
      val lhs = Vector(1, 1)
      val rhs = Vector(1, 1)

      val expected_result = List(
        Vector(1, 0, 1, 0),
        Vector(1, 0, 0, 1),
        Vector(0, 1, 1, 0),
        Vector(0, 1, 0, 1))

      val r = LankfordSolver solve (lhs, rhs)

      (r) must contain (exactly (expected_result:_*)) 
    }

    "new solve the equation x_1 + x_2 = y_1 + y_2 + y_3" in {
      val lhs = Vector(1, 1)
      val rhs = Vector(1, 1, 1)

      val expected_result = List(
        Vector(1, 0, 1, 0, 0),
        Vector(1, 0, 0, 1, 0),
        Vector(1, 0, 0, 0, 1),
        Vector(0, 1, 1, 0, 0),
        Vector(0, 1, 0, 1, 0),
        Vector(0, 1, 0, 0, 1))

      val r = LankfordSolver solve (lhs, rhs)
      (r) must contain (exactly (expected_result:_*))
    }

    "new solve the equation 2x_1 + x_2 +x_3= 2y_1 + y_2" in {
      val lhs = Vector(2, 1, 1)
      val rhs = Vector(2, 1)

      val expected_result = List(
        Vector(1, 0, 0, 1, 0),
        Vector(0, 1, 0, 0, 1),
        Vector(0, 0, 1, 0, 1),
        Vector(1, 0, 0, 0, 2),
        Vector(0, 2, 0, 1, 0),
        Vector(0, 1, 1, 1, 0),
        Vector(0, 0, 2, 1, 0))

      val r = LankfordSolver solve (lhs, rhs)
      //      println("===")
      //      println(r)
      //      println("===")
      //      println(expected_result)

      (r) must contain (exactly (expected_result:_*))
    }

    "new solve the equation x_1 = y_1 + y_2" in {
      val lhs = Vector(1)
      val rhs = Vector(1, 1)

      val expected_result = List(
        Vector(1, 1, 0),
        Vector(1, 0, 1))

      val r = LankfordSolver solve (lhs, rhs)
      (r) must contain (exactly (expected_result:_*))    
    }
  }
}

