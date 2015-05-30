/*
 * Tests for verit's interface.
**/

package at.logic.gapt.provers.veriT

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.FSequent
import org.specs2.mutable._

class VeriTProverTest extends Specification {

  val veriT = new VeriTProver()

  args( skipAll = !veriT.isInstalled )

  "VeriT" should {
    "prove a v not a" in {
      //skipped("--proof-version in isValid is only supported on Giselle's machine")
      val a = FOLAtom( "a", Nil )
      val f = Or( a, Neg( a ) )

      veriT.isValid( f ) must beEqualTo( true )
    }

    "parse the proof of a |- a" in {
      val a = FOLAtom( "a" )
      val s = FSequent( List( a ), List( a ) )

      veriT.getExpansionSequent( s ) must not be None
    }

    "prove top" in { veriT.getExpansionSequent( FSequent( Seq(), Seq( Top() ) ) ) must beSome }
    "not prove bottom" in { veriT.getExpansionSequent( FSequent( Seq(), Seq( Bottom() ) ) ) must beNone }
    "not refute top" in { veriT.getExpansionSequent( FSequent( Seq( Top() ), Seq() ) ) must beNone }
    "refute bottom" in { veriT.getExpansionSequent( FSequent( Seq( Bottom() ), Seq() ) ) must beSome }
  }
}
