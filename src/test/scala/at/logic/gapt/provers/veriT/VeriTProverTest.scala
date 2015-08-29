/*
 * Tests for verit's interface.
**/

package at.logic.gapt.provers.veriT

import at.logic.gapt.examples.BussTautology
import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansionTrees.toDeep
import at.logic.gapt.proofs.lk.base.{ Sequent, HOLSequent }
import at.logic.gapt.provers.sat4j.Sat4jProver
import org.specs2.mutable._

class VeriTProverTest extends Specification {

  val veriT = new VeriTProver()

  args( skipAll = !veriT.isInstalled )

  "VeriT" should {
    "prove a v not a" in {
      val a = FOLAtom( "a", Nil )
      val f = Or( a, Neg( a ) )

      veriT.isValid( f ) must beEqualTo( true )
    }

    "parse the proof of a |- a" in {
      val a = FOLAtom( "a" )
      val s = HOLSequent( List( a ), List( a ) )

      veriT.getExpansionSequent( s ) must not be None
    }

    "prove top" in {
      veriT.getExpansionSequent( HOLSequent( Seq(), Seq( Top() ) ) ) must beSome
    }

    "not prove bottom" in {
      veriT.getExpansionSequent( HOLSequent( Seq(), Seq( Bottom() ) ) ) must beNone
    }

    "not refute top" in {
      veriT.getExpansionSequent( HOLSequent( Seq( Top() ), Seq() ) ) must beNone
    }

    "refute bottom" in {
      veriT.getExpansionSequent( HOLSequent( Seq( Bottom() ), Seq() ) ) must beSome
    }

    "validate the buss tautology for n=1" in {
      veriT.isValid( BussTautology( 1 ) ) must beTrue
    }

    "handle predicate named exists" in {
      val seq = FOLAtom( "exists" ) +: Sequent() :+ FOLAtom( "exists" )
      veriT isValid seq must_== true
      veriT getExpansionSequent seq must beSome
    }

    "handle unicode names" in {
      val sequent = ( Eq( FOLConst( "α" ), FOLConst( "β" ) ) +:
        Sequent()
        :+ Eq( FOLFunction( "f", FOLConst( "α" ) ), FOLFunction( "f", FOLConst( "β" ) ) ) )
      new Sat4jProver().isValid( toDeep( veriT getExpansionSequent sequent get ) ) must_== true
    }
  }
}
