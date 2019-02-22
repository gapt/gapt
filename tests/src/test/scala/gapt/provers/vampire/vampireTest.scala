package gapt.provers.vampire

import gapt.examples.CountingEquivalence
import gapt.expr._
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Top
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLVar
import gapt.proofs.Clause
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentMatchers
import gapt.proofs.context.mutable.MutableContext
import gapt.utils.SatMatchers
import org.specs2.mutable._

class VampireTest extends Specification with SequentMatchers with SatMatchers {

  args( skipAll = !Vampire.isInstalled )

  "The Vampire interface" should {
    "refute { :- P; P :- }" in {
      val p = FOLAtom( "P", Nil )
      val s1 = HOLSequent( Nil, p :: Nil )
      val s2 = HOLSequent( p :: Nil, Nil )
      Vampire getResolutionProof ( s1 :: s2 :: Nil ) must beSome
    }
  }

  "The Vampire interface" should {
    "prove SKKx = Ix : { :- f(a,x) = x; :- f(f(f(b,x),y),z) = f(f(x,z), f(y,z)); :- f(f(c,x),y) = x; f(f(f(b,c),c),x) = f(a,x) :- }" in {
      val x = FOLVar( "x" )
      val y = FOLVar( "y" )
      val z = FOLVar( "z" )
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val c = FOLConst( "c" )
      val fax = FOLFunction( "f", a :: x :: Nil )
      val fbx = FOLFunction( "f", b :: x :: Nil )
      val fcx = FOLFunction( "f", c :: x :: Nil )
      val fffbxyz = FOLFunction( "f", FOLFunction( "f", fbx :: y :: Nil ) :: z :: Nil )
      val fxz = FOLFunction( "f", x :: z :: Nil )
      val fyz = FOLFunction( "f", y :: z :: Nil )
      val ffxzfyz = FOLFunction( "f", fxz :: fyz :: Nil )
      val ffcxy = FOLFunction( "f", fcx :: y :: Nil )
      val fbc = FOLFunction( "f", b :: c :: Nil )
      val fffbccx = FOLFunction( "f", FOLFunction( "f", fbc :: c :: Nil ) :: x :: Nil )

      val i = Eq( fax, x )
      val s = Eq( fffbxyz, ffxzfyz )
      val k = Eq( ffcxy, x )
      val skk_i = Eq( fffbccx, fax )

      val s1 = HOLSequent( Nil, List( i ) )
      val s2 = HOLSequent( Nil, List( k ) )
      val s3 = HOLSequent( Nil, List( s ) )
      val t1 = HOLSequent( List( skk_i ), Nil )
      Vampire getResolutionProof List( s1, s2, s3, t1 ) must beSome
    }
  }

  "The Vampire interface" should {
    "not refute { :- P; Q :- }" in {
      val s1 = HOLSequent( Nil, List( FOLAtom( "P", Nil ) ) )
      val t1 = HOLSequent( List( FOLAtom( "Q", Nil ) ), Nil )
      Vampire getResolutionProof List( s1, t1 ) must beNone
    }
  }

  "Vampire" should {
    "prove identity" in {
      val s = Sequent() :+ hof"k=k"
      Vampire.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "prove { A or B :- -(-A and -B)  }" in {
      val s = hof"A | B" +: Sequent() :+ hof"-(-A & -B)"
      Vampire.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "handle quantified antecedents" in {
      val seq = hof"!x 0+x=x" +: hof"!x!y s(x)+y=s(x+y)" +: Sequent() :+ hof"s(0)+s(s(0)) = s(s(s(0)))"
      Vampire.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "prove top" in { Vampire.getLKProof( HOLSequent( Seq(), Seq( Top() ) ) ) must beSome }
    "not prove bottom" in { Vampire.getLKProof( HOLSequent( Seq(), Seq( Bottom() ) ) ) must beNone }
    "not refute top" in { Vampire.getLKProof( HOLSequent( Seq( Top() ), Seq() ) ) must beNone }
    "refute bottom" in { Vampire.getLKProof( HOLSequent( Seq( Bottom() ), Seq() ) ) must beSome }

    "ground sequents" in {
      val seq = hof"x=y" +: Sequent() :+ hof"y=x"
      Vampire.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "treat variables in sequents as constants" in {
      val seq = hof"P(x)" +: Sequent() :+ hof"P(c)"
      Vampire.getExpansionProof( seq ) must beNone
    }

    "handle weird sequents" in {
      val cnf = Set( Clause(), hoa"a" +: Clause() )
      Vampire.getResolutionProof( cnf ) must beSome
    }

    "large cnf" in { Vampire getResolutionProof CountingEquivalence( 2 ) must beSome }

    "smt splitting" in {
      val smtVampire = new Vampire( extraArgs = Seq( "-sas", "z3" ) )
      if ( !smtVampire.isInstalled ) skipped
      smtVampire getExpansionProof hof"""
          a=b | b=c | c=d | !x f x = g x ->
            f a = f b | f b = f c | f c = f d | f a = g a
        """ must beLike {
        case Some( proof ) => proof.deep must beEValidSequent
      }
    }
  }

  "splitting definitions" in {
    val formula = CountingEquivalence( 2 )
    implicit val ctx: MutableContext = MutableContext.guess( formula )
    val Some( proof ) = Vampire.getResolutionProof( formula )
    ctx.check( proof )
    ok
  }

  "casc mode" in {
    VampireCASC.getResolutionProof( CountingEquivalence( 2 ) ) must beSome
  }

}
