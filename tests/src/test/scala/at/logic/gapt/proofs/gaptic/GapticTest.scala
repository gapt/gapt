package at.logic.gapt.proofs.gaptic

import at.logic.gapt.proofs.Sequent
import at.logic.gapt.expr._
import org.specs2.mutable.Specification

class GapticTest extends Specification {

  "rewrite simple" in {
    Lemma(
      ( "ass" -> hof"P(f(a))" ) +:
        ( "eq" -> hof"!x f(x) = g(x)" ) +:
        Sequent()
        :+ ( "goal" -> hof"P(g(a))" )
    ) {
        rewrite rtl "eq" in "goal"
        prop
      }
    ok
  }
  "rewrite addition" in {
    Lemma(
      ( "add0" -> hof"!x x+0 = x" ) +:
        ( "adds" -> hof"!x!y x+s(y) = s(x+y)" ) +:
        Sequent()
        :+ ( "goal" -> hof"s(s(0)) + s(s(0)) = s(s(s(s(0))))" )
    ) {
        rewrite.many ltr ( "add0", "adds" ) in "goal"
        axiomRefl
      }
    ok
  }

}
