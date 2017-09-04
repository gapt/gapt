package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import org.specs2.mutable._

class SkolemizationTest extends Specification {

  "Skolemization" should {
    val x = Var( "x", Ti )
    val y = Var( "y", Ti )
    val f = All( x, Atom( Const( "P", Ti -> To ), x :: Nil ) )
    val p = Const( "P", Ti -> To )
    val r = Const( "R", Ti -> ( Ti -> To ) )

    "leave a formula with only weak quantifiers untouched" in {
      skolemize( f, Polarity.InAntecedent ) must_== f
    }

    "introduce correctly a Skolem constant" in {
      val stream = new SkolemSymbolFactory( Seq() ).getSkolemSymbols
      val skfun = Const( stream.head, Ti )
      val skf = Atom( p, skfun :: Nil )
      skolemize( f, Polarity.InSuccedent, Seq(), stream ) must beEqualTo( skf )
    }

    "handle a binary formula correctly" in {
      val stream = new SkolemSymbolFactory( Seq() ).getSkolemSymbols
      val y = Var( "y", Ti )
      val rxy = Atom( r, x :: y :: Nil )
      val f2 = Imp( f, All( x, Ex( y, rxy ) ) )

      val skfun0 = Const( stream.head, Ti )
      val skfun1 = HOLFunction( Const( stream.tail.head, Ti -> Ti ), x :: Nil )
      val skf1 = Atom( p, skfun0 :: Nil )
      val skf2 = Atom( r, x :: skfun1 :: Nil )

      val skf = Imp( skf1, All( x, skf2 ) )
      skolemize( f2, Polarity.InAntecedent, Seq(), stream ) must beEqualTo( skf )

      // now we skolemize the skolemize formula, with opposite polarity
      val skfun2 = Const( stream.tail.tail.head, Ti )
      val skfun3 = HOLFunction( Const( stream.tail.head, Ti -> Ti ), skfun2 :: Nil )
      val skf3 = Atom( r, skfun2 :: skfun3 :: Nil )
      val skf4 = Imp( skf1, skf3 )
      skolemize( skolemize( f2, Polarity.InAntecedent, Seq(), stream ), Polarity.InSuccedent, Seq(), stream.tail ) must beEqualTo( skf4 )
    }

    "handle a simple proof correctly" in {
      val s5 = "s_1"
      val cs5 = Const( s5, Ti )
      val alpha = Var( "α", Ti )
      val Palpha = Atom( p, alpha :: Nil )
      val Ps0 = Atom( p, cs5 :: Nil )
      val allxPx = All( x, Atom( p, x :: Nil ) )
      val ax = LogicalAxiom( Palpha )
      val proof = ForallRightRule(
        ForallLeftRule(
          ax,
          allxPx, alpha ),
        allxPx, alpha )

      val ax_sk = LogicalAxiom( Ps0 )
      val proof_sk = ForallLeftRule( ax_sk, allxPx, cs5 )

      skolemize( proof ) must_== proof_sk
    }

    "work for a cut-free proof (1)" in {
      /* Proof is:
                 R(a,b) :- R(a,b)
                 ----------------------   Ex,r
                 R(a,b) :- ex y. R(a,y)
            ---------------------------   Ex,l
            ex y.R(a,y) :- ex y. R(a,y)
      ---------------------------------- All,l
      all x.ex y.R(x,y) :- ex y. R(a,y)
      --------------------------------------- All,r
      all x.ex y.R(x,y) :- all x.ex y. R(x,y)

      Skolemized: (wrote s0 instead of s_{0} for easier reading)
          R(s1,s0(s1)) :- R(s1,s0(s1))
          ----------------------------   Ex,r
          R(s1,s0(s1)) :- ex y. R(s1,y)
      ---------------------------------- All,l
      all x.R(x,s0(x)) :- ex y. R(s1,y)
       */

      val a = Var( "a", Ti )
      val b = Var( "b", Ti )
      val Rab = Atom( r, a :: b :: Nil )
      val exyRay = Ex( y, Atom( r, a :: y :: Nil ) )
      val allxexyRxy = All( x, Ex( y, Atom( r, x :: y :: Nil ) ) )
      val ax = LogicalAxiom( Rab )
      val r1 = ExistsRightRule( ax, exyRay, b )
      val r2 = ExistsLeftRule( r1, exyRay, b )
      val r3 = ForallLeftRule( r2, allxexyRxy, a )
      val proof: LKProof = ForallRightRule( r3, allxexyRxy, a )

      val fs0 = Const( "s_0", Ti -> Ti )
      val s1c = Const( "s_1", Ti )
      val s0s1 = App( fs0, s1c )
      val sR = Atom( r, List( s1c, s0s1 ) )
      val sax = LogicalAxiom( sR )

      val exyRs1y = Ex( y, Atom( r, List( s1c, y ) ) )
      //      val exyRs1s0s1 = Ex( y, Atom( r, List(a,y) ) )
      val sr1 = ExistsRightRule( sax, exyRs1y, s0s1 )

      val allxRxs0x = All( x, Atom( r, List( x, App( fs0, x ) ) ) )
      val sr2 = ForallLeftRule( sr1, allxRxs0x, s1c )
      val proof_sk = sr2

      skolemize( proof ) must_== proof_sk
    }

  }
}
