package at.logic.gapt.provers.leancop

import at.logic.gapt.examples.BussTautology
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class LeanCoPProverTest extends Specification with SatMatchers {
  args( skipAll = !LeanCoP.isInstalled )

  "LeanCoP" should {
    "LEM" in {
      val a = FOLAtom( "a" )
      val f = Or( a, Neg( a ) )
      LeanCoP.isValid( f ) must beTrue
    }

    "a |- a" in {
      val a = FOLAtom( "a" )
      val s = HOLSequent( Seq( a ), Seq( a ) )

      LeanCoP.getExpansionProof( s ) must beSome
    }

    "forall x, P(x) |- P(0)" in {
      val f = All( FOLVar( "x" ), FOLAtom( "P", FOLVar( "x" ) ) )
      val g = FOLAtom( "P", FOLConst( "0" ) )

      LeanCoP.getExpansionProof( HOLSequent( Seq( f ), Seq( g ) ) ) must beSome
    }

    "x + 0 = x, x + s(y) = s(x+y) |- x + s(0) = s(x)" in {
      val seq = hof"!x x+0 = x" +: hof"!x !y x+s(y) = s(x+y)" +: Sequent() :+ hof"k+s(0) = s(k)"
      LeanCoP.getExpansionProof( seq ) must beSome
    }

    "P,P->Q |- Q" in {
      val seq = HOLSequent( Seq( FOLAtom( "P" ), Imp( FOLAtom( "P" ), FOLAtom( "Q" ) ) ), Seq( FOLAtom( "Q" ) ) )
      LeanCoP.getExpansionProof( seq ) must beSome
    }

    "linear example" in {
      LeanCoP getExpansionProof hof"p 0 & !x (p x -> p (s x)) -> p (s (s (s 0)))" must beLike {
        case Some( expansion ) =>
          expansion.deep must beValidSequent
      }
    }

    "validate the buss tautology for n=2" in { LeanCoP.isValid( BussTautology( 2 ) ) must beTrue }

    "not prove a or b" in { LeanCoP getExpansionProof hof"a | b" must beNone }

    "prove top" in { LeanCoP.getLKProof( Sequent() :+ Top() ) must beSome }
    "not prove bottom" in { LeanCoP.getLKProof( Sequent() :+ Bottom() ) must beNone }
    "not refute top" in { LeanCoP.getLKProof( Top() +: Sequent() ) must beNone }
    "refute bottom" in { LeanCoP.getLKProof( Bottom() +: Sequent() ) must beSome }
  }
}
