package at.logic.gapt.proofs.gaptic

import at.logic.gapt.proofs.Sequent
import org.specs2.mutable.Specification
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._

class GapticTest extends Specification {

  "rewrite simple" in {
    Lemma(
      ( "ass" -> parseFormula( "P(f(a))" ) ) +:
        ( "eq" -> parseFormula( "(all x f(x) = g(x))" ) ) +:
        Sequent()
        :+ ( "goal" -> parseFormula( "P(g(a))" ) )
    ) {
        rewrite rtl "eq" in "goal"
        prop
      }
    ok
  }
  "rewrite addition" in {
    Lemma(
      ( "add0" -> parseFormula( "(all x x + 0 = x)" ) ) +:
        ( "adds" -> parseFormula( "(all x all y x + s(y) = s(x + y))" ) ) +:
        Sequent()
        :+ ( "goal" -> parseFormula( "s(s(0)) + s(s(0)) = s(s(s(s(0))))" ) )
    ) {
        rewrite.many ltr ( "add0", "adds" ) in "goal"
        axiomRefl
      }
    ok
  }

}
