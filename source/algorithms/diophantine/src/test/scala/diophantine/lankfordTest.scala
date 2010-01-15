package at.logic.algorithms.diophantine

import org.specs.SpecificationWithJUnit

//import org.specs.specification

class LankfordSolverTest extends SpecificationWithJUnit {
  "The Lankford Diophantine solver" should {
      "solve the equation x_1 + x_2 + x_3 = y_1 + y_2 + y_3" in {
        val ls = new LankfordSolver[String]
        val list = List((1,"x1"), (1,"x2"),(1,"x3"),(1,"x4"))
        val expected_result = List(
          List((1,"x1"), (0,"x2"), (0,"x3"), (0,"x4")),
          List((0,"x1"), (1,"x2"), (0,"x3"), (0,"x4")),
          List((0,"x1"), (0,"x2"), (1,"x3"), (0,"x4")), 
          List((0,"x1"), (0,"x2"), (0,"x3"), (1,"x4")))
//        val list = List((1,"x"), (2,"y"))
        val r  = ls.solve(list, 1 )
        /*
        try {
          //println(r)
          for (x <- r) {
            for (y <- x) {
              y match {
                case (c,_) => print(c+" ");
              }
            }
            println("");
          }

          println(r.map(MathHelperFunctions.sumOfCoefficients[String]))
          //val eqn = MathHelperFunctions.mergeCoefficientsWithSolutions(list, r)
          //println(MathHelperFunctions.sumOfSolvedEquation(eqn))
        } catch {
          case x : Exception => println(x.getMessage)
          case _ => println("Unknown Exception!")
        } */

        r must beEqual (expected_result)
      }
  }
}