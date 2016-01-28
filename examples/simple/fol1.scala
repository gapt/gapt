package at.logic.gapt.examples

import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{ parseFormula, parseTerm }
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object fol1 {
  val p = Lemma( Sequent(
    Seq( "L" -> parseFormula( "(all x all y (P(x,y) -> Q(x,y)))" ) ),
    Seq( "R" -> parseFormula( "(exists x exists y (-Q(x,y) -> -P(x,y)))" ) )
  ) ) {

    cut( parseFormula( "(all x exists y (-P(x,y) | Q(x,y)))" ), "C" )

    // left subproof
    allR( "C" )
    exR( parseTerm( "a" ), "C" )
    allL( parseTerm( "x" ), "L" )
    allL( parseTerm( "a" ), "L_0" )
    decompose
    destruct( "L_0_0" )
    repeat( axiomLog )

    // right subproof
    allL( parseTerm( "b" ), "C" )
    exL( "C_0" )
    exR( parseTerm( "b" ), "R" )
    exR( parseTerm( "y" ), "R_0" )
    destruct( "C_0" )
    repeat( decompose andThen axiomLog )
  }
}
