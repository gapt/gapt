package at.logic.gapt.examples

import at.logic.gapt.expr.FOLVar
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
    forget( "R" )
    allR( FOLVar( "z" ) )
    exR( parseTerm( "a" ) )
    allL( parseTerm( "z" ) )
    allL( parseTerm( "a" ) )
    orR( "C1" )
    impL( "L2" )
    negR( "C1_1" )
    axiomLog
    axiomLog

    // right subproof
    forget( "L" )
    allL( parseTerm( "b" ) )
    exL( FOLVar( "v" ) )
    exR( parseTerm( "b" ) )
    exR( parseTerm( "v" ) )
    forget( "C" )
    forget( "R" )
    forget( "R1" )
    impR( "R2" )
    negR( "R2_2" )
    negL( "R2_1" )
    orL( "C1" )
    negL( "C1" )
    axiomLog
    axiomLog
  }
}
