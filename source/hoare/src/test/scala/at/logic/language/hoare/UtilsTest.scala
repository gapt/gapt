package at.logic.language.hoare

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class UtilsTest extends SpecificationWithJUnit with ProgramTestUtils {
  "LoopFree" should {
    "match loop-free programs" in {
      LoopFree.unapply(program("skip")) must beSome
      LoopFree.unapply(program("if P() then skip else skip fi")) must beSome
      LoopFree.unapply(program("x := a; skip")) must beSome
    }

    "not match for loops" in {
      LoopFree.unapply(program("for x < y do skip od")) must beNone
    }

    "not match for loops, even if nested" in {
      LoopFree.unapply(program("if P() then for x < y do skip od else skip fi")) must beNone
      LoopFree.unapply(program("for x < y do skip od; skip")) must beNone
    }
  }

  "mapVariableNames" should {
    "rename lhs of assignments" in {
      mapVariableNames(program("x := a"), { _ + "_1" }) must beEqualTo(program("x_1 := a"))
    }

    "rename inside expressions" in {
      mapVariableNames(program("if P(x,y) then x := f(y) else y := g(x) fi"), { _ + "_1"}) must
        beEqualTo(program("if P(x_1,y_1) then x_1 := f(y_1) else y_1 := g(x_1) fi"))
    }
  }

  "weakestPrecondition" should {
    "handle ifs" in {
      weakestPrecondition(program("if P(x) then x := f(y) else x := f(z) fi"), formula("R(x)")) must
        beEqualTo(formula("And Imp P(x) R(f(y)) Imp Neg P(x) R(f(z))"))
    }
  }

  "unrollLoop" should {
    "be loop-free" in {
      unrollLoop(program("for y < z do x := +(x,y) od"), 4) must beLike {
        case LoopFree(_) => ok
        case _ => ko
      }
    }
  }

  "blocks" should {
    "split sequences" in {
      Blocks.unapply(program("x := x; x:= x; x := x")) must beEqualTo(List.fill(3)(program("x := x")))
    }
  }
}
