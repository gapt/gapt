package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{ parseFormula, parseTerm }

object tape extends TacticsProof {
  implicit var ctx = FiniteContext()
  ctx += Context.Sort( "i" )
  ctx += hoc"f: i>i"
  ctx += hoc"'+': i>i>i"
  ctx += hoc"0: i"; ctx += hoc"1: i"
  ctx += ( "A" -> hof"!x (f(x) = 0 | f(x) = 1)" )
  ctx += ( "I" -> le"^v !x?y f(x+y) = v" )

  val lhs = Lemma( ( "A" -> fof"A" ) +: Sequent()
    :+ ( "I0" -> fof"I(0)" ) :+ ( "I1" -> fof"I(1)" ) ) {
    unfold( "I0", "I" )
    unfold( "I1", "I" )
    allR( "I0", FOLVar( "x_0" ) )
    allR( "I1", FOLVar( "x_1" ) )
    exR( "I0", fot"x_1" )
    forget( "I0" )
    exR( "I1", fot"x_0" )
    forget( "I1" )
    unfold( "A", "A" )
    allL( fot"x_0 + x_1" )
    forget( "A" )
    destruct( "A_0" )
    trivial
    forget( "I0_0" )
    axiomTh
  }

  val rhs = Lemma( ( "Iv" -> fof"I(v)" ) +: Sequent()
    :+ ( "C" -> fof"?x?y (x != y & f x = f y)" ) ) {
    unfold( "Iv", "I" )
    allL( fot"0" )
    exL( "Iv_0", fov"y_0" )
    allL( fot"y_0 + 1" )
    forget( "Iv" )
    exL( "Iv_1", fov"y_1" )
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
    :+ ( "C" -> fof"?x?y (x != y & f x = f y)" ) ) {
    cut( fof"I(1)", "I1" )
    cut( fof"I(0)", "I0" )
    insert( lhs )
    forget( "A" )
    forget( "I1" )
    insert( rhs )
    insert( rhs )
  }

  val defs = ctx.definitions
}
