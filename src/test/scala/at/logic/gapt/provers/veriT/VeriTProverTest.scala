/*
 * Tests for verit's interface.
**/

package at.logic.gapt.provers.veriT

import at.logic.gapt.examples.BussTautology
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Sequent, HOLSequent }
import at.logic.gapt.proofs.expansion.toDeep
import at.logic.gapt.provers.sat.Sat4j
import org.specs2.mutable._

class VeriTProverTest extends Specification {
  args( skipAll = !VeriT.isInstalled )

  "VeriT" should {
    "prove a v not a" in {
      val a = FOLAtom( "a", Nil )
      val f = Or( a, Neg( a ) )

      VeriT.isValid( f ) must beEqualTo( true )
    }

    "parse the proof of a |- a" in {
      val a = FOLAtom( "a" )
      val s = HOLSequent( List( a ), List( a ) )

      VeriT.getExpansionSequent( s ) must not be None
    }

    "prove top" in {
      VeriT.getExpansionSequent( HOLSequent( Seq(), Seq( Top() ) ) ) must beSome
    }

    "not prove bottom" in {
      VeriT.getExpansionSequent( HOLSequent( Seq(), Seq( Bottom() ) ) ) must beNone
    }

    "not refute top" in {
      VeriT.getExpansionSequent( HOLSequent( Seq( Top() ), Seq() ) ) must beNone
    }

    "refute bottom" in {
      VeriT.getExpansionSequent( HOLSequent( Seq( Bottom() ), Seq() ) ) must beSome
    }

    "validate the buss tautology for n=1" in {
      VeriT.isValid( BussTautology( 1 ) ) must beTrue
    }

    "handle predicate named exists" in {
      val seq = FOLAtom( "exists" ) +: Sequent() :+ FOLAtom( "exists" )
      VeriT isValid seq must_== true
      VeriT getExpansionSequent seq must beSome
    }

    "handle unicode names" in {
      val sequent = ( Eq( FOLConst( "α" ), FOLConst( "β" ) ) +:
        Sequent()
        :+ Eq( FOLFunction( "f", FOLConst( "α" ) ), FOLFunction( "f", FOLConst( "β" ) ) ) )
      Sat4j.isValid( toDeep( VeriT getExpansionSequent sequent get ) ) must_== true
    }
  }
}
