package gapt.examples

import gapt.expr._
import gapt.expr.formula.fol.FOLVar
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object tape extends TacticsProof {
  ctx += Sort( "i" )
  ctx += hoc"f: i>i"
  ctx += hoc"'+': i>i>i"
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += hoc"0: i"; ctx += hoc"1: i"
  ctx += hof"A = (∀x (f(x) = 0 ∨ f(x) = 1))"
  ctx += hof"I(v) = (∀x ∃y f(x+y) = v)"

  ctx += "add_comm" -> hcl":- x+y = y+x"
  ctx += "add_assoc" -> hcl":- (x+y)+z = x+(y+z)"
  ctx += "zero_add" -> hcl":- 0+x = x"
  ctx += "add_one_neq" -> hcl"x+y+1 = x :-"

  val lhs = Lemma( ( "A" -> fof"A" ) +: Sequent()
    :+ ( "I0" -> fof"I(0)" ) :+ ( "I1" -> fof"I(1)" ) ) {
    unfold( "I" ).in( "I0", "I1" )
    allR( "I0", FOLVar( "x_0" ) )
    allR( "I1", FOLVar( "x_1" ) )
    exR( "I0", fov"x_1" )
    forget( "I0" )
    exR( "I1", fov"x_0" )
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
    exR( "C", fov"y_0", fot"(y_0 + y_1) + 1" )
    forget( "C" )
    destruct( "C_0" )
    negR
    foTheory
    rewrite rtl "Iv_1" in "Iv_0"
    foTheory
  }

  val proof = Lemma( ( "A" -> fof"A" ) +: Sequent()
    :+ ( "C" -> fof"?x?y (x != y & f x = f y)" ) ) {
    cut( "I1", fof"I(1)" ) right insert( rhs )
    cut( "I0", fof"I(0)" ) right insert( rhs )
    insert( lhs )
  }
}
