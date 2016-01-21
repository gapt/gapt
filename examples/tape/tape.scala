package at.logic.gapt.examples

import at.logic.gapt.expr.FOLVar
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{ parseFormula, parseTerm }

object tape {
  val A = parseFormula( "(all x ( f(x) = 0 | f(x) = 1 ))" )
  val I0 = parseFormula( "(all x exists y f( x + y ) = 0)" )
  val I1 = parseFormula( "(all x exists y f( x + y ) = 1)" )
  val Iv = parseFormula( "(all x exists y f( x + y ) = v)" )

  val lhs = Lemma( Sequent( Seq( "A" -> parseFormula( "A" ) ), Seq( "I0" -> parseFormula( "I(0)" ), "I1" -> parseFormula( "I(1)" ) ) ) ) {
    defR( "I0", I0 )
    defR( "I1", I1 )
    allR( FOLVar( "x_0" ), "I0" )
    allR( FOLVar( "x_1" ), "I1" )
    exR( parseTerm( "x_0" ) )
    forget( "I1" )
    exR( parseTerm( "x_1" ) )
    forget( "I0" )
    defL( "A", A )
    allL( parseTerm( "x_0 + x_1" ) )
    forget( "A" )
    destruct
    axiom
    forget( "I0'" )
    axiomTh
  }

  val rhs = Lemma( Sequent( Seq( "Iv" -> parseFormula( "I(v)" ) ), Seq( "C" -> parseFormula( "(exists x exists y ( -x=y & f(x)=f(y) ))" ) ) ) ) {
    defL( "Iv", Iv )
    allL( parseTerm( "0" ) )
    exL( FOLVar( "y_0" ), "Iv1" )
    allL( parseTerm( "y_0 + 1" ) )
    forget( "Iv" )
    exL( FOLVar( "y_1" ), "Iv2" )
    exR( parseTerm( "y_0" ) )
    exR( parseTerm( "(y_0 + y_1) + 1" ) )
    forget( "C" )
    forget( "C'" )
    destruct
    negR
    forget( "Iv1" )
    forget( "Iv2" )
    axiomTh
    eqL( "Iv2", "Iv1" )
    forget( "Iv2" )
    axiomTh
  }

  val p = Lemma( Sequent( Seq( "A" -> parseFormula( "A" ) ), Seq( "C" -> parseFormula( "(exists x exists y ( -x=y & f(x)=f(y) ))" ) ) ) ) {
    cut( parseFormula( "I(1)" ), "I1" )
    cut( parseFormula( "I(0)" ), "I0" )
    forget( "C" ) // should not be necessary
    insert( lhs )
    forget( "A" )
    forget( "I1" )
    insert( rhs )
  }
}
