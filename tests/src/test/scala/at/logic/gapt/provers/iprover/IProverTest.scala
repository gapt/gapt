package at.logic.gapt.provers.iprover

import at.logic.gapt.examples.CountingEquivalence
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ naive, thresholds }
import at.logic.gapt.proofs.{ Clause, HOLSequent, Sequent, SequentMatchers }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class IProverTest extends Specification with SequentMatchers with SatMatchers {
  args( skipAll = !IProver.isInstalled )
  "IProver" should {
    "prove identity" in {
      val s = Sequent() :+ hof"k=k"
      IProver.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "prove { A or B :- -(-A and -B)  }" in {
      val s = hof"A | B" +: Sequent() :+ hof"-(-A & -B)"
      IProver.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "handle quantified antecedents" in {
      val seq = hof"!x 0+x=x" +: hof"!x!y s(x)+y=s(x+y)" +: Sequent() :+ hof"s(0)+s(s(0)) = s(s(s(0)))"
      IProver.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "prove top" in { IProver.getLKProof( HOLSequent( Seq(), Seq( Top() ) ) ) must beSome }
    "not prove bottom" in { IProver.getLKProof( HOLSequent( Seq(), Seq( Bottom() ) ) ) must beNone }
    "not refute top" in { IProver.getLKProof( HOLSequent( Seq( Top() ), Seq() ) ) must beNone }
    "refute bottom" in { IProver.getLKProof( HOLSequent( Seq( Bottom() ), Seq() ) ) must beSome }

    "ground sequents" in {
      val seq = hof"x=y" +: Sequent() :+ hof"y=x"
      IProver.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "treat variables in sequents as constants" in {
      val seq = hof"P(x)" +: Sequent() :+ hof"P(c)"
      IProver getExpansionProof seq must beNone
    }

    "handle weird sequents" in {
      val cnf = Set( Clause(), hoa"a" +: Clause() )
      IProver.getResolutionProof( cnf ) must beSome
    }

    "counting 0" in { IProver.getResolutionProof( CountingEquivalence( 0 ) ) must beSome }
    "counting 1" in { IProver.getResolutionProof( CountingEquivalence( 1 ) ) must beSome }
    "counting 2" in { IProver.getResolutionProof( CountingEquivalence( 2 ) ) must beSome }
    "counting 3" in { IProver.getResolutionProof( CountingEquivalence( 3 ) ) must beSome }
  }

}
