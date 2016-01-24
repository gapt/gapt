package at.logic.gapt.examples

import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._

object lkTests {
  val eqLemma = Lemma(
    Sequent( Seq( "c" -> parseFormula( "P(y) & Q(y)" ), "eq1" -> parseFormula( "u = v" ), "eq2" -> parseFormula( "y = x" ), "a" -> parseFormula( "P(u) -> Q(u)" ) ), Seq( "b" -> parseFormula( "P(x) & Q(x)" ) ) )
  ) {
      eqL( "eq1", "a" ).to( parseFormula( "P(v) -> Q(v)" ) )
      eqL( "eq1", "a" ).to( parseFormula( "P(v) -> Q(u)" ) )
      eqR( "eq2", "b" ).fromRightToLeft
      axiom
    }

  val defLemma = Lemma(
    Sequent( Seq( "c" -> parseFormula( "P(b) | Q(b)" ), "a" -> parseFormula( "P(u) -> Q(u)" ) ), Seq( "b" -> parseFormula( "P(x) & Q(x)" ) ) )
  ) {
      defL( "a", parseFormula( "P(a) -> Q(a)" ) )
      defR( "b", parseFormula( "P(b) | Q(b)" ) )
      axiom
    }
}