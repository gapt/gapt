package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{ parseFormula, parseTerm }

object tape {
  val A = p9f"(all x ( f(x) = 0 | f(x) = 1 ))"
  val I0 = p9f"(all x exists y f( x + y ) = 0)"
  val I1 = p9f"(all x exists y f( x + y ) = 1)"
  val Iv = p9f"(all x exists y f( x + y ) = v)"

  val lhs = Lemma( ( "A" -> p9f"A" ) +: Sequent()
    :+ ( "I0" -> p9f"I(0)" ) :+ ( "I1" -> p9f"I(1)" ) ) {
    defR( "I0", I0 )
    defR( "I1", I1 )
    allR( FOLVar( "x_0" ), "I0" )
    allR( FOLVar( "x_1" ), "I1" )
    exR( p9t"x_1", "I0" )
    forget( "I0" )
    exR( p9t"x_0", "I1" )
    forget( "I1" )
    defL( "A", A )
    allL( p9t"x_0 + x_1" )
    forget( "A" )
    destruct( "A_0" )
    axiom
    forget( "I0_0" )
    axiomTh
  }

  val rhs = Lemma( ( "Iv" -> p9f"I(v)" ) +: Sequent()
    :+ ( "C" -> p9f"(exists x exists y ( -x=y & f(x)=f(y) ))" ) ) {
    defL( "Iv", Iv )
    allL( p9t"0" )
    exL( FOLVar( "y_0" ), "Iv_0" )
    allL( p9t"y_0 + 1" )
    forget( "Iv" )
    exL( FOLVar( "y_1" ), "Iv_1" )
    exR( p9t"y_0", "C" )
    exR( p9t"(y_0 + y_1) + 1", "C_0" )
    forget( "C" )
    forget( "C_0" )
    destruct( "C_0_0" )
    negR
    forget( "Iv_0" )
    forget( "Iv_1" )
    axiomTh
    eqL( "Iv_1", "Iv_0" )
    forget( "Iv_1" )
    axiomTh
  }

  val p = Lemma( ( "A" -> p9f"A" ) +: Sequent()
    :+ ( "C" -> p9f"(exists x exists y ( -x=y & f(x)=f(y) ))" ) ) {
    cut( p9f"I(1)", "I1" )
    cut( p9f"I(0)", "I0" )
    insert( lhs )
    forget( "A" )
    forget( "I1" )
    insert( rhs )
    insert( rhs )
  }

  val defs = Map(
    FOLAtom( "A" ) -> A,
    FOLAtomConst( "I", 1 ) -> Abs( FOLVar( "v" ), Iv )
  )
}
