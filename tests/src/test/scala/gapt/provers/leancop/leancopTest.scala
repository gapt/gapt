package gapt.provers.leancop

import gapt.examples.BussTautology
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Bottom
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLVar
import gapt.proofs.{ HOLSequent, Sequent }
import gapt.utils.SatMatchers
import org.specs2.mutable._

class LeanCoPProverTest extends Specification with SatMatchers {
  args( skipAll = !LeanCoP.isInstalled )

  "LEM" in {
    val a = FOLAtom( "a" )
    val f = Or( a, Neg( a ) )
    LeanCoP.isValid( f ) must beTrue
  }

  "taut" in {
    val a = FOLAtom( "a" )
    val s = HOLSequent( Seq( a ), Seq( a ) )

    LeanCoP.getExpansionProof( s ) must beSome( havingTautDeepSequent )
  }

  "forall x, P(x) |- P(0)" in {
    val f = All( FOLVar( "x" ), FOLAtom( "P", FOLVar( "x" ) ) )
    val g = FOLAtom( "P", FOLConst( "0" ) )

    LeanCoP.getExpansionProof( HOLSequent( Seq( f ), Seq( g ) ) ) must beSome( havingTautDeepSequent )
  }

  "plus one equals succ" in {
    val seq = hos"!x x+0 = x, !x !y x+s(y) = s(x+y) :- k+s(0) = s(k)"
    LeanCoP.getExpansionProof( seq ) must beSome( havingQTautDeepSequent )
  }

  "P,P->Q |- Q" in {
    val seq = HOLSequent( Seq( FOLAtom( "P" ), Imp( FOLAtom( "P" ), FOLAtom( "Q" ) ) ), Seq( FOLAtom( "Q" ) ) )
    LeanCoP.getExpansionProof( seq ) must beSome( havingTautDeepSequent )
  }

  "linear example" in {
    LeanCoP getExpansionProof hof"p 0 & !x (p x -> p (s x)) -> p (s (s (s 0)))" must beSome( havingTautDeepSequent )
  }

  "validate the buss tautology for n=2" in { LeanCoP.isValid( BussTautology( 2 ) ) must beTrue }

  "not prove a or b" in { LeanCoP getExpansionProof hof"a | b" must beNone }

  "prove top" in { LeanCoP.getLKProof( Sequent() :+ Top() ) must beSome }
  "not prove bottom" in { LeanCoP.getLKProof( Sequent() :+ Bottom() ) must beNone }
  "not refute top" in { LeanCoP.getLKProof( Top() +: Sequent() ) must beNone }
  "refute bottom" in { LeanCoP.getLKProof( Bottom() +: Sequent() ) must beSome }
}
