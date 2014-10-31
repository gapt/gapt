package at.logic.parsing.hoare

import at.logic.language.fol._
import at.logic.language.hoare._
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class ProgramParserTest extends SpecificationWithJUnit with ProgramTestUtils {
  "ProgramParser" should {
    "parse an assignment" in {
      program("x := f(x)") must beEqualTo(Assign("x", term("f(x)")))
    }
    "parse a skip" in {
      program("skip") must beEqualTo(Skip())
    }
    "parse an if-then-else" in {
      program("if P() then skip else x := a fi") must beEqualTo(
        IfElse(Atom("P"), Skip(), Assign("x", term("a"))))
    }
    "parse a sequence" in {
      program("x := a; skip") must beEqualTo(Sequence(Assign("x", term("a")), Skip()))
      program("x := a; x := b; x := c") must beEqualTo(
        Sequence(program("x := a"), Sequence(program("x := b"), program("x := c"))))
    }
    "parse a for loop" in {
      program("for x < y do skip od") must beEqualTo(ForLoop("x", "y", Skip()))
    }
  }
}
