package at.logic.language.hoare

import at.logic.parsing.hoare.ProgramParser
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import ProgramParser._

@RunWith(classOf[JUnitRunner])
class UtilsTest extends SpecificationWithJUnit {
  "LoopFree" should {
    "match loop-free programs" in {
      LoopFree.unapply(parseProgram("skip")) must beSome
      LoopFree.unapply(parseProgram("if P() then skip else skip fi")) must beSome
      LoopFree.unapply(parseProgram("x := a; skip")) must beSome
    }

    "not match for loops" in {
      LoopFree.unapply(parseProgram("for x < y do skip od")) must beNone
    }

    "not match for loops, even if nested" in {
      LoopFree.unapply(parseProgram("if P() then for x < y do skip od else skip fi")) must beNone
      LoopFree.unapply(parseProgram("for x < y do skip od; skip")) must beNone
    }
  }

  "mapVariableNames" should {
    "rename lhs of assignments" in {
      mapVariableNames(parseProgram("x := a"), { _ + "_1" }) must beEqualTo(parseProgram("x_1 := a"))
    }

    "rename inside expressions" in {
      mapVariableNames(parseProgram("if P(x,y) then x := f(y) else y := g(x) fi"), { _ + "_1"}) must
        beEqualTo(parseProgram("if P(x_1,y_1) then x_1 := f(y_1) else y_1 := g(x_1) fi"))
    }
  }

  "weakestPrecondition" should {
    "handle ifs" in {
      weakestPrecondition(parseProgram("if P(x) then x := f(y) else x := f(z) fi"), parseFormula("R(x)")) must
        beEqualTo(parseFormula("(P(x) -> R(f(y))) & (-P(x) -> R(f(z)))"))
    }
  }

  "unrollLoop" should {
    "be loop-free" in {
      unrollLoop(parseProgram("for y < z do x := x + y od"), 4) must beLike {
        case LoopFree(_) => ok
        case _ => ko
      }
    }
  }

  "blocks" should {
    "split sequences" in {
      Blocks.unapply(parseProgram("x := x; x:= x; x := x")) must beEqualTo(List.fill(3)(parseProgram("x := x")))
    }
  }
}
