package gapt.provers.spass

import gapt.examples.CountingEquivalence
import gapt.expr._
import gapt.expr.fol.{ naive, thresholds }
import gapt.proofs.resolution.{ AvatarComponent, AvatarNegNonGroundComp, ResolutionToLKProof }
import gapt.proofs.{ Clause, HOLSequent, MutableContext, Sequent, SequentMatchers }
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class SpassTest extends Specification with SequentMatchers with SatMatchers {
  args( skipAll = !SPASS.isInstalled )
  "SPASS" should {
    "prove identity" in {
      val s = Sequent() :+ hof"k=k"
      SPASS.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "prove { A or B :- -(-A and -B)  }" in {
      val s = hof"A | B" +: Sequent() :+ hof"-(-A & -B)"
      SPASS.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "handle quantified antecedents" in {
      val seq = hof"!x 0+x=x" +: hof"!x!y s(x)+y=s(x+y)" +: Sequent() :+ hof"s(0)+s(s(0)) = s(s(s(0)))"
      SPASS.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "prove top" in { SPASS.getLKProof( HOLSequent( Seq(), Seq( Top() ) ) ) must beSome }
    "not prove bottom" in { SPASS.getLKProof( HOLSequent( Seq(), Seq( Bottom() ) ) ) must beNone }
    "not refute top" in { SPASS.getLKProof( HOLSequent( Seq( Top() ), Seq() ) ) must beNone }
    "refute bottom" in { SPASS.getLKProof( HOLSequent( Seq( Bottom() ), Seq() ) ) must beSome }

    "ground sequents" in {
      val seq = hof"x=y" +: Sequent() :+ hof"y=x"
      SPASS.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "treat variables in sequents as constants" in {
      val seq = hof"P(x)" +: Sequent() :+ hof"P(c)"
      SPASS getExpansionProof seq must beNone
    }

    "handle weird sequents" in {
      val cnf = Set( Clause(), hoa"a" +: Clause() )
      SPASS.getResolutionProof( cnf ) must beSome
    }

    "large cnf" in {
      SPASS getExpansionProof CountingEquivalence( 3 ) must beLike { case Some( p ) => p.deep must beValidSequent }
    }

    "bug with quantified splitting" in {
      SPASS getExpansionProof CountingEquivalence( 2 ) must beLike { case Some( p ) => p.deep must beValidSequent }
    }

    "bug with ground parts in quantified splits" in {
      val Some( res ) = SPASS.getResolutionProof( CountingEquivalence( 1 ) )
      res.subProofs.collect { case AvatarComponent( c: AvatarNegNonGroundComp ) => c } must not( beEmpty )
      ResolutionToLKProof( res )
      ok
    }

    "splitting definitions" in {
      val formula = CountingEquivalence( 2 )
      implicit val ctx: MutableContext = MutableContext.guess( formula )
      val Some( proof ) = SPASS.getResolutionProof( formula )
      ctx.check( proof )
      ok
    }
  }

}
