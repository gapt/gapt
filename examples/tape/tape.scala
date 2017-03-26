package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic._

object tape extends TacticsProof {
  ctx += Context.Sort( "i" )
  ctx += hoc"f: i>i"
  ctx += hoc"'+': i>i>i"
  ctx += hoc"0: i"; ctx += hoc"1: i"
  ctx += hof"A = (∀x (f(x) = 0 ∨ f(x) = 1))"
  ctx += hof"I(v) = (∀x ∃y f(x+y) = v)"

  Seq(
    hof"∀x∀y x+y = y+x",
    hof"∀x∀y∀z (x+y)+z = x+(y+z)",
    hof"∀x 0+x = x",
    hof"∀x∀y x+y+1 != x"
  ).flatMap( CNFp( _ ) ).foreach( ctx += _ )

  val lhs = Lemma( ( "A" -> fof"A" ) +: Sequent()
    :+ ( "I0" -> fof"I(0)" ) :+ ( "I1" -> fof"I(1)" ) ) {
    unfold( "I" ) in ( "I0", "I1" )
    allR( "I0", FOLVar( "x_0" ) )
    allR( "I1", FOLVar( "x_1" ) )
    exR( "I0", fot"x_1" )
    forget( "I0" )
    exR( "I1", fot"x_0" )
    forget( "I1" )
    unfold( "A" ) in "A"
    allL( fot"x_0 + x_1" )
    forget( "A" )
    destruct( "A_0" )
    trivial
    foTheory
  }

  val rhs = Lemma( ( "Iv" -> fof"I(v)" ) +: Sequent()
    :+ ( "C" -> fof"?x?y (x != y & f x = f y)" ) ) {
    unfold( "I" ) in "Iv"
    allL( fot"0" )
    exL( "Iv_0", fov"y_0" )
    allL( fot"y_0 + 1" )
    forget( "Iv" )
    exL( "Iv_1", fov"y_1" )
    exR( "C", fot"y_0", fot"(y_0 + y_1) + 1" )
    forget( "C" )
    destruct( "C_0" )
    negR
    foTheory
    rewrite rtl "Iv_1" in "Iv_0"
    foTheory
  }

  val proof = Lemma( ( "A" -> fof"A" ) +: Sequent()
    :+ ( "C" -> fof"?x?y (x != y & f x = f y)" ) ) {
    cut( "I1", fof"I(1)" )
    cut( "I0", fof"I(0)" )
    insert( lhs )
    repeat( insert( rhs ) )
  }
}
