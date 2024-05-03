/*
 * Tests for verit's interface.
**/

package gapt.provers.verit

import gapt.examples.BussTautology
import gapt.expr._
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLAtomConst
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.proofs.{ HOLSequent, Sequent }
import gapt.provers.sat.Sat4j
import gapt.utils.SatMatchers
import org.specs2.mutable._

class VeriTProverTest extends Specification with SatMatchers {
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

      VeriT.getExpansionProof( s ) must not be None
    }

    "prove top" in {
      VeriT.getExpansionProof( HOLSequent( Seq(), Seq( Top() ) ) ) must beSome
    }

    "not prove bottom" in {
      VeriT.getExpansionProof( HOLSequent( Seq(), Seq( Bottom() ) ) ) must beNone
    }

    "not refute top" in {
      VeriT.getExpansionProof( HOLSequent( Seq( Top() ), Seq() ) ) must beNone
    }

    "refute bottom" in {
      VeriT.getExpansionProof( HOLSequent( Seq( Bottom() ), Seq() ) ) must beSome
    }

    "validate the buss tautology for n=1" in {
      VeriT.isValid( BussTautology( 1 ) ) must beTrue
    }

    "handle predicate named exists" in {
      val seq = FOLAtom( "exists" ) +: Sequent() :+ FOLAtom( "exists" )
      VeriT isValid seq must_== true
      VeriT getExpansionProof seq must beSome
    }

    "handle unicode names" in {
      val sequent = ( Eq( FOLConst( "α" ), FOLConst( "β" ) ) +:
        Sequent()
        :+ Eq( FOLFunction( "f", FOLConst( "α" ) ), FOLFunction( "f", FOLConst( "β" ) ) ) )
      Sat4j.isValid( ( VeriT getExpansionProof sequent get ).deep ) must_== true
    }

    "term level booleans" in {
      val f = Const( "f", To ->: Ti )
      val p = FOLAtomConst( "p", 1 )
      val formula = ( f( Top() ) === f( Bottom() ) ) --> ( p( f( Bottom() ) ) <-> p( f( Top() ) ) )
      val Some( expansion ) = VeriT getExpansionProof ( Sequent() :+ formula ): @unchecked
      expansion.deep must beValidSequent
    }
  }
}
