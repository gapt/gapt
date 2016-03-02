package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.TheoryAxiom

object tape extends TacticsProof {
  implicit var ctx = FiniteContext()
  ctx += Context.Sort( "i" )
  ctx += hoc"f: i>i"
  ctx += hoc"'+': i>i>i"
  ctx += hoc"0: i"; ctx += hoc"1: i"
  ctx += hof"A = (∀x (f(x) = 0 ∨ f(x) = 1))"
  ctx += hof"I(v) = (∀x ∃y f(x+y) = v)"

  val ax1 = TheoryAxiom( hoa"f(0+x) = f(x+1+y)" +: Sequent() :+ hoa"f(x) = f(x+y+1)" )
  val ax2 = TheoryAxiom( hoa"f(x+y) = 1" +: Sequent() :+ hoa"f(y+x)=1" )
  val ax3 = TheoryAxiom( hoa"x = x+y+1" +: Sequent() )

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
    insert( ax2 )
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
    insert( ax3 )
    rewrite rtl "Iv_1" in "Iv_0"
    insert( ax1 )
  }

  val p = Lemma( ( "A" -> fof"A" ) +: Sequent()
    :+ ( "C" -> fof"?x?y (x != y & f x = f y)" ) ) {
    cut( fof"I(1)", "I1" )
    cut( fof"I(0)", "I0" )
    insert( lhs )
    repeat( insert( rhs ) )
  }

  val defs = ctx.definitions
}
