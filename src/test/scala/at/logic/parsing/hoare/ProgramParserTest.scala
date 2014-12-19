package at.logic.parsing.hoare

import at.logic.language.fol._
import at.logic.language.hoare._
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import ProgramParser._

@RunWith(classOf[JUnitRunner])
class ProgramParserTest extends SpecificationWithJUnit {
  "ProgramParser" should {
    "parse an assignment" in {
      parseProgram("x := f(x)") must beEqualTo(Assign("x", parseTerm("f(x)")))
    }
    "parse a skip" in {
      parseProgram("skip") must beEqualTo(Skip())
    }
    "parse an if-then-else" in {
      parseProgram("if P() then skip else x := a fi") must beEqualTo(
        IfElse(Atom("P"), Skip(), Assign("x", parseTerm("a"))))
    }
    "parse a sequence" in {
      parseProgram("x := a; skip") must beEqualTo(Sequence(Assign("x", parseTerm("a")), Skip()))
      parseProgram("x := a; x := b; x := c") must beEqualTo(
        Sequence(parseProgram("x := a"), Sequence(parseProgram("x := b"), parseProgram("x := c"))))
    }
    "parse a for loop" in {
      parseProgram("for x < y do skip od") must beEqualTo(ForLoop("x", "y", Skip()))
    }
  }
}
