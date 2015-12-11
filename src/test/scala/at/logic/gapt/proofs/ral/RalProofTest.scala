package at.logic.gapt.proofs.ral

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Clause, Ant, Suc, Sequent }
import RalProof.Label

import org.specs2.mutable._

class RalProofTest extends Specification {

  // Daniel's PhD thesis, p. 110
  "simple example" in {
    val f = Const( "f", Ti -> Ti )
    val X0 = Var( "X0", Ti -> To ).asInstanceOf[Var with HOLPartialAtom]
    val Y0 = Var( "Y0", Ti -> To ).asInstanceOf[Var with HOLPartialAtom]
    val x = Var( "x", Ti )
    val x0 = Var( "x0", Ti )
    val g = Const( "g", ( Ti -> To ) -> Ti )
    val T = Abs( X0, Abs( x, X0( x ) --> X0( f( x ) ) ) )

    val p1 = RalInitial( Sequent() :+ ( Label( Y0, T ) -> All( x, Y0( x ) --> Y0( f( x ) ) ) ) )
    val p2 = RalAllT( p1, Suc( 0 ), x0 )
    val p3 = RalImpT( p2, Suc( 0 ) )
    val p4 = RalSub( p3, Substitution( x0 -> g( Y0 ) ) )
    val p5 = RalInitial( Sequent() :+ ( Label( Y0 ) -> Y0( g( Y0 ) ) ) )
    val p6 = RalCut( p5, Seq( Suc( 0 ) ), p4, Seq( Ant( 0 ) ) )
    val p7 = RalSub( p3, Substitution( x0 -> f( g( Y0 ) ) ) )
    val p8 = RalCut( p6, Seq( Suc( 0 ) ), p7, Seq( Ant( 0 ) ) )
    val formula: HOLFormula = Y0( f( f( g( Y0 ) ) ) )
    val p9 = RalInitial( ( Label( Y0 ) -> formula ) +: Sequent() )
    val p10 = RalCut( p8, Seq( Suc( 0 ) ), p9, Seq( Ant( 0 ) ) )
    p10.conclusion must_== Clause()
  }

  "work on simple proofs" in {
    val x = Var( "X", To ).asInstanceOf[Var with HOLAtom]
    val p = FOLAtom( "P" )

    // FIXME: the old RalResolutionTest used (exists x, x) as an axiom and then applied forall-right...
    // I've got no idea what that was supposed to do. --Gabriel
    val i1 = RalInitial( Sequent() :+ ( Label() -> All( x, x ) ) )
    val i2 = RalAllT( i1, Suc( 0 ), x )
    val i3 = RalSub( i2, Substitution( x -> ( p & -p ) ) )
    val i4 = RalAndT1( i3, Suc( 0 ) )
    val i5 = RalAndT2( i3, Suc( 0 ) )
    val i6 = RalNegT( i5, Suc( 0 ) )
    val i7 = RalCut( i4, Seq( Suc( 0 ) ), i6, Seq( Ant( 0 ) ) )

    i7.conclusion must_== Clause()
  }

  "work on non-idempotent substitutions" in {
    val x = Var( "x", Ti )
    val f = Const( "f", Ti -> Ti )
    val p = HOLAtomConst( "P", Ti )

    val i1 = RalInitial( Sequent() :+ ( Label() -> p( x ) ) )
    val i2 = RalSub( i1, Substitution( x -> f( x ) ) )

    i2.formulas must_== ( Clause() :+ p( f( x ) ) )
  }

}
