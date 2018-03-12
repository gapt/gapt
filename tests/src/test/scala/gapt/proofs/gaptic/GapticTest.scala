package gapt.proofs.gaptic

import gapt.proofs.Sequent
import gapt.expr._
import org.specs2.mutable.Specification

class GapticTest extends Specification {

  "rewrite simple" in {
    Proof(
      ( "ass" -> hof"P(f(a))" ) +:
        ( "eq" -> hof"!x f(x) = g(x)" ) +:
        Sequent()
        :+ ( "goal" -> hof"P(g(a))" ) ) {
        rewrite rtl "eq" in "goal"
        prop
      }
    ok
  }
  "rewrite addition" in {
    Proof(
      ( "add0" -> hof"!x x+0 = x" ) +:
        ( "adds" -> hof"!x!y x+s(y) = s(x+y)" ) +:
        Sequent()
        :+ ( "goal" -> hof"s(s(0)) + s(s(0)) = s(s(s(s(0))))" ) ) {
        rewrite.many ltr ( "add0", "adds" ) in "goal"
        axiomRefl
      }
    ok
  }

}
