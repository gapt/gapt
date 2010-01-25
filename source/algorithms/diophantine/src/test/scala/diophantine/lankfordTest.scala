package at.logic.algorithms.diophantine

import org.specs.SpecificationWithJUnit

//import org.specs.specification

class LankfordSolverTest extends SpecificationWithJUnit {
  "The Lankford Diophantine solver" should {
      val ls = new LankfordSolver[String]

      "solve the equation x_1 + x_2 = y_1 + y_2" in {
        val lhs = List((1,"x1"), (1,"x2"))
        val rhs = List((1,"y1"), (1,"y2"))
        

        val expected_result = List(
          List((1,"x1"), (0,"x2"), (1,"y1"), (0,"y2")),
          List((1,"x1"), (0,"x2"), (0,"y1"), (1,"y2")),
          List((0,"x1"), (1,"x2"), (1,"y1"), (0,"y2")),
          List((0,"x1"), (1,"x2"), (0,"y1"), (1,"y2")))
        val r  = ls.solve(lhs,rhs )


        //println("every expected result is in the results")
        for(l <- expected_result) {
          //println(l)
          r.contains(l) must beTrue
        }
        //println("every result is expected")
        for(l <- r) {
          //println(l)
          expected_result.contains(l) must beTrue
        }
      }

    "solve the equation x_1 + x_2 = y_1 + y_2 + y_3" in {
      val lhs = List((1,"x1"), (1,"x2"))
      val rhs = List((1,"y1"), (1,"y2"),(1,"y3"))


      val expected_result = List(
        List((1,"x1"), (0,"x2"), (1,"y1"), (0,"y2"), (0,"y3")),
        List((1,"x1"), (0,"x2"), (0,"y1"), (1,"y2"), (0,"y3")),
        List((1,"x1"), (0,"x2"), (0,"y1"), (0,"y2"), (1,"y3")),
        List((0,"x1"), (1,"x2"), (1,"y1"), (0,"y2"), (0,"y3")),
        List((0,"x1"), (1,"x2"), (0,"y1"), (1,"y2"), (0,"y3")),
        List((0,"x1"), (1,"x2"), (0,"y1"), (0,"y2"), (1,"y3")))

      val r  = ls.solve(lhs,rhs )


      //println("every expected result is in the results")
      for(l <- expected_result) {
        //println(l)
        r.contains(l) must beTrue
      }
      //println("every result is expected")
      for(l <- r) {
        //println(l)
        expected_result.contains(l) must beTrue
      }
    }

  }
}

