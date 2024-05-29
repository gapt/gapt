package gapt.formats.hoare

import gapt.expr._
import gapt.proofs.hoare._
import org.specs2.mutable._
import ProgramParser._
import gapt.expr.formula.fol.FOLAtom

class ProgramParserTest extends Specification {
  "ProgramParser" should {
    "parse an assignment" in {
      parseProgram("x := f(x)") must beEqualTo(Assign("x", parseTerm("f(x)")))
    }
    "parse a skip" in {
      parseProgram("skip") must beEqualTo(Skip())
    }
    "parse an if-then-else" in {
      parseProgram("if P() then skip else x := a fi") must beEqualTo(
        IfElse(FOLAtom("P"), Skip(), Assign("x", parseTerm("a")))
      )
    }
    "parse a sequence" in {
      parseProgram("x := a; skip") must beEqualTo(Sequence(Assign("x", parseTerm("a")), Skip()))
      parseProgram("x := a; x := b; x := c") must beEqualTo(
        Sequence(parseProgram("x := a"), Sequence(parseProgram("x := b"), parseProgram("x := c")))
      )
    }
    "parse a for loop" in {
      parseProgram("for x < y do skip od") must beEqualTo(ForLoop("x", "y", Skip()))
    }
  }
}
