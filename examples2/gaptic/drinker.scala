package at.logic.gapt.examples

import at.logic.gapt.expr.FOLVar
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object drinker {
  val drinker = Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" ) ) ) ) {
    exR( parseTerm( "c" ) )
    impR
    allR( FOLVar( "y_0" ) )
    exR( parseTerm( "y_0" ) )
    impR
    allR( FOLVar( "y_1" ) )
    axiomLog
  }

  val dualdrinker = Lemma( Sequent( Seq( "D" -> parseFormula( "(all x (P(x) & (exists y -P(y))))" ) ), Nil ) ) {
    allL( parseTerm( "c" ) )
    andL
    exL( FOLVar( "y_0" ) )
    negL
    allL( parseTerm( "y_0" ) )
    andL
    exL( FOLVar( "y_1" ) )
    negL
    axiomLog
  }

  val drinker2 = Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" ) ) ) ) {
    exR( parseTerm( "c" ) )
    impR
    allR
    exR( parseTerm( "y" ) )
    impR
    allR
    axiomLog
  }

  val drinker3 = Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" ) ) ) ) {
    exR( parseTerm( "c" ) )
    impR
    allR
    exR( parseTerm( "y" ) )
    impR
    allR
    axiom
  }

  val dualdrinker2 = Lemma( Sequent( Seq( "D" -> parseFormula( "(all x (P(x) & (exists y -P(y))))" ) ), Nil ) ) {
    allL( parseTerm( "c" ) )
    andL
    exL
    negL
    allL( parseTerm( "y" ) )
    andL
    exL
    negL
    axiomLog
  }
}
