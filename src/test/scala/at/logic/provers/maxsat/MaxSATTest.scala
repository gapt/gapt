/*
 * Tests for the MaxSAT interface.
**/

package at.logic.provers.maxsat

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.calculi.resolution._
import at.logic.language.fol._

@RunWith(classOf[JUnitRunner])
class MaxSATTest extends SpecificationWithJUnit {
  val box: Set[FClause] = Set()

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
  object SimpleMaxSATFormula {
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
      if (!new MaxSAT(MaxSATSolver.QMaxSAT).isInstalled) skipped("qmaxsat not installed")

      val (hard, soft) = SimpleMaxSATFormula()
      (new MaxSAT(MaxSATSolver.QMaxSAT)).solvePWM(hard, soft) must beLike {
        case Some(model) => if (model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x2) == true &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x1) == false &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x3) == false) ok
        else ko
        case None => ko
      }
    }
  }

  "ToySAT" should {

    "deal correctly with a simple instance" in {
      if (!new MaxSAT(MaxSATSolver.ToySolver).isInstalled) skipped("toysolver not installed")

      val (hard, soft) = SimpleMaxSATFormula()
      (new MaxSAT(MaxSATSolver.ToySAT)).solvePWM(hard, soft) must beLike {
        case Some(model) => if (model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x2) == true &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x1) == false &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x3) == false) ok
        else ko
        case None => ko
      }
    }
  }

  "ToySolver" should {

    "deal correctly with a simple instance" in {
      if (!new MaxSAT(MaxSATSolver.ToySolver).isInstalled) skipped("toysolver not installed")

      val (hard, soft) = SimpleMaxSATFormula()
      (new MaxSAT(MaxSATSolver.ToySolver)).solvePWM(hard, soft) must beLike {
        case Some(model) => if (model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x2) == true &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x1) == false &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x3) == false) ok
        else ko
        case None => ko
      }
    }
  }

  "MiniMaxSAT" should {

    "deal correctly with a simple instance" in {
      if (!new MaxSAT(MaxSATSolver.MiniMaxSAT).isInstalled) skipped("minimaxsat not installed")

      val (hard, soft) = SimpleMaxSATFormula()
      (new MaxSAT(MaxSATSolver.MiniMaxSAT)).solvePWM(hard, soft) must beLike {
        case Some(model) => if (model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x2) == true &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x1) == false &&
          model.asInstanceOf[MapBasedInterpretation].interpret(SimpleMaxSATFormula.x3) == false) ok
        else ko
        case None => ko
      }
    }
  }
}
