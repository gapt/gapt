package at.logic.gapt.provers.eprover

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ SequentMatchers, Clause, HOLSequent, Sequent }
import org.specs2.mutable._

class EProverTest extends Specification with SequentMatchers {
  args( skipAll = !EProver.isInstalled )
  "EProver" should {
    "prove identity" in {
      val s = Sequent() :+ hof"k=k"
      EProver.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "prove { A or B :- -(-A and -B)  }" in {
      val s = hof"A | B" +: Sequent() :+ hof"-(-A & -B)"
      EProver.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "handle quantified antecedents" in {
      val seq = hof"!x 0+x=x" +: hof"!x!y s(x)+y=s(x+y)" +: Sequent() :+ hof"s(0)+s(s(0)) = s(s(s(0)))"
      EProver.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "prove top" in { EProver.getLKProof( HOLSequent( Seq(), Seq( Top() ) ) ) must beSome }
    "not prove bottom" in { EProver.getLKProof( HOLSequent( Seq(), Seq( Bottom() ) ) ) must beNone }
    "not refute top" in { EProver.getLKProof( HOLSequent( Seq( Top() ), Seq() ) ) must beNone }
    "refute bottom" in { EProver.getLKProof( HOLSequent( Seq( Bottom() ), Seq() ) ) must beSome }

    "ground sequents" in {
      val seq = hof"x=y" +: Sequent() :+ hof"y=x"
      EProver.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "treat variables in sequents as constants" in {
      val seq = hof"P(x)" +: Sequent() :+ hof"P(c)"
      EProver getExpansionProof seq must beNone
    }

    "handle weird sequents" in {
      val cnf = Set( Clause(), hoa"a" +: Clause() )
      EProver.getRobinsonProof( cnf ) must beSome
    }
  }

}
