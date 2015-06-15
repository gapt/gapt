package at.logic.gapt.provers.leancop

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.FSequent
import org.specs2.mutable._

class LeanCoPProverTest extends Specification {

  val leanCoP = new LeanCoPProver()

  args( skipAll = !leanCoP.isInstalled )

  "LeanCoP" should {
    //    "LEM" in {
    //      val a = FOLAtom( "a" )
    //      val f = Or( a, Neg( a ) )
    //      leanCoP.isValid( f ) must beTrue
    //    }

    "a |- a" in {
      val a = FOLAtom( "a" )
      val s = FSequent( Seq( a ), Seq( a ) )

      leanCoP.getExpansionSequent( s ) must beSome
    }

    "forall x, P(x) |- P(0)" in {
      val f = All( FOLVar( "x" ), FOLAtom( "P", FOLVar( "x" ) ) )
      val g = FOLAtom( "P", FOLConst( "0" ) )

      leanCoP.getExpansionSequent( FSequent( Seq( f ), Seq( g ) ) ) must beSome
    }

    //    "validate the buss tautology for n=1" in { leanCoP.isValid( BussTautology( 1 ) ) must beTrue }

    // infix ops, top/bottom cannot be parsed yet
  }
}
