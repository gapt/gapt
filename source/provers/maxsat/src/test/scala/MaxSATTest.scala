/*
 * Tests for the MiniSAT interface.
**/

package at.logic.provers.maxsat


import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol._
import at.logic.calculi.resolution._

@RunWith(classOf[JUnitRunner])
class MaxSATTest extends SpecificationWithJUnit {
  val box: Set[FClause] = Set()

  args(skipAll = !(new MaxSAT(MaxSATSolver.QMaxSAT)).isInstalled() || !(new MaxSAT(MaxSATSolver.ToySAT)).isInstalled() || !(new MaxSAT(MaxSATSolver.ToySolver)).isInstalled())

  /*
   * Simple instance for testing wether weighted partial MaxSAT
   * is called correctly and solves the instance.
   * Hard:
   *   x1 v x2
   *   x2 v x3
   *   x1 v x2 v x3
   * Soft: [minimizes the amount of variables to be true]
   *   -x1
   *   -x2
   *   -x3
   */
  object SimpleQMaxSATFormula {
    val c1 = FOLConst("c1")
    val c2 = FOLConst("c2")
    val c3 = FOLConst("c3")

    val x1 = Atom("X", c1 :: Nil)
    val x2 = Atom("X", c2 :: Nil)
    val x3 = Atom("X", c3 :: Nil)

    val h1 = Or(x1, x2)
    val h2 = Or(x2, x3)
    val h3 = Or(Or(x1, x2), x3)

    val s1 = (Neg(x1), 1)
    val s2 = (Neg(x2), 1)
    val s3 = (Neg(x3), 1)

    def apply() = {

      val hard = Set(h1, h2, h3)
      val soft = Set(s1, s2, s3)

      (hard, soft)
    }
  }

  "QMaxSAT" should {

    "deal correctly with a simple instance" in {
      val (hard, soft) = SimpleQMaxSATFormula()
      (new MaxSAT(MaxSATSolver.QMaxSAT)).solvePWM(hard, soft) must beLike {
        case Some(model) => if (model.asInstanceOf[MapBasedInterpretation].interpret(SimpleQMaxSATFormula.x2) == true &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleQMaxSATFormula.x1) == false &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleQMaxSATFormula.x3) == false) ok
        else ko
        case None => ko
      }
    }
  }

  "ToySAT" should {

    "deal correctly with a simple instance" in {
      val (hard, soft) = SimpleQMaxSATFormula()
      (new MaxSAT(MaxSATSolver.ToySAT)).solvePWM(hard, soft) must beLike {
        case Some(model) => if (model.asInstanceOf[MapBasedInterpretation].interpret(SimpleQMaxSATFormula.x2) == true &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleQMaxSATFormula.x1) == false &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleQMaxSATFormula.x3) == false) ok
        else ko
        case None => ko
      }
    }
  }

  "ToySolver" should {

    "deal correctly with a simple instance" in {
      val (hard, soft) = SimpleQMaxSATFormula()
      (new MaxSAT(MaxSATSolver.ToySolver)).solvePWM(hard, soft) must beLike {
        case Some(model) => if (model.asInstanceOf[MapBasedInterpretation].interpret(SimpleQMaxSATFormula.x2) == true &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleQMaxSATFormula.x1) == false &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleQMaxSATFormula.x3) == false) ok
        else ko
        case None => ko
      }
    }
  }
}
