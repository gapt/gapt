package at.logic.gapt.provers.leancop

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula

import org.specs2.mutable._

class LeanCoPProverTest extends Specification {
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
      val seq = HOLSequent(
        Seq( "x+0 = x", "x+s(y) = s(x+y)" ).map( s => univclosure( parseFormula( s ) ) ),
        Seq( parseFormula( "k+s(0) = s(k)" ) )
      )

      LeanCoP.getExpansionProof( seq ) must beSome
    }

    "P,P->Q |- Q" in {
      val seq = HOLSequent( Seq( FOLAtom( "P" ), Imp( FOLAtom( "P" ), FOLAtom( "Q" ) ) ), Seq( FOLAtom( "Q" ) ) )
      LeanCoP.getExpansionProof( seq ) must beSome
    }

    //    "validate the buss tautology for n=1" in { leanCoP.isValid( BussTautology( 1 ) ) must beTrue }

    // top/bottom cannot be parsed yet
  }
}
