package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{ parseFormula, parseTerm }

object tape {
  val A = fof"(all x ( f(x) = 0 | f(x) = 1 ))"
  val I0 = fof"(all x exists y f( x + y ) = 0)"
  val I1 = fof"(all x exists y f( x + y ) = 1)"
  val Iv = fof"(all x exists y f( x + y ) = v)"

  val lhs = Lemma( ( "A" -> fof"A" ) +: Sequent()
    :+ ( "I0" -> fof"I(0)" ) :+ ( "I1" -> fof"I(1)" ) ) {
    defR( "I0", I0 )
    defR( "I1", I1 )
    allR( FOLVar( "x_0" ), "I0" )
    allR( FOLVar( "x_1" ), "I1" )
    exR( "I0", fot"x_1" )
    forget( "I0" )
    exR( "I1", fot"x_0" )
    forget( "I1" )
    defL( "A", A )
    allL( fot"x_0 + x_1" )
    forget( "A" )
    destruct( "A_0" )
    trivial
    forget( "I0_0" )
    axiomTh
  }

  val rhs = Lemma( ( "Iv" -> fof"I(v)" ) +: Sequent()
    :+ ( "C" -> fof"(exists x exists y ( -x=y & f(x)=f(y) ))" ) ) {
    defL( "Iv", Iv )
    allL( fot"0" )
    exL( FOLVar( "y_0" ), "Iv_0" )
    allL( fot"y_0 + 1" )
    forget( "Iv" )
    exL( FOLVar( "y_1" ), "Iv_1" )
    exR( "C", fot"y_0", fot"(y_0 + y_1) + 1" )
    forget( "C" )
    destruct( "C_0" )
    negR
    forget( "Iv_0" )
    forget( "Iv_1" )
    axiomTh
    eqL( "Iv_1", "Iv_0" )
    forget( "Iv_1" )
    axiomTh
  }

  val p = Lemma( ( "A" -> fof"A" ) +: Sequent()
    :+ ( "C" -> fof"(exists x exists y ( -x=y & f(x)=f(y) ))" ) ) {
    cut( fof"I(1)", "I1" )
    cut( fof"I(0)", "I0" )
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
