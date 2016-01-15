package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import org.specs2.mutable._

class SubstitutionTest extends Specification with SequentMatchers {
  "Substitutions" should {
    object proof1 {
      val x = FOLVar( "x" )
      val P = FOLAtomConst( "P", 1 )
      val a = FOLConst( "a" )
      val f = FOLFunctionConst( "f", 1 )

      val ax1 = LogicalAxiom( P( x ) )
      val ax2 = LogicalAxiom( P( x ) )
      val proof = CutRule( ax1, Suc( 0 ), ax2, Ant( 0 ) )
      val subst = Substitution( x, f( a ) )
    }

    object proof2 {
      val x = FOLVar( "x" )
      val y = FOLVar( "y" )
      val P = FOLAtomConst( "P", 2 )
      val pxy = HOLAtom( P, List( x, y ) )
      val allxpx = All( x, P( x, y ) )
      val ax1 = LogicalAxiom( P( x, y ) )
      val r1 = ForallLeftRule( ax1, allxpx, x )
      val proof = ForallRightRule( r1, allxpx, x )

      val a = FOLConst( "a" )
      val f = FOLFunctionConst( "f", 1 )
      val subst = Substitution( y, f( a ) )
      val subst2 = Substitution( y, x ) //test for overbinding
    }

    "apply correctly to a simple proof" in {
      import proof1._
      val p_s = applySubstitution( subst )( proof )
      p_s.endSequent must beMultiSetEqual( P( f( a ) ) +: Sequent() :+ P( f( a ) ) )
    }

    "apply correctly to a proof with quantifiers" in {
      import proof2._
      val p_s = applySubstitution( subst )( proof )
      val pfa = All( x, P( x, f( a ) ) )
      p_s.endSequent must beMultiSetEqual( pfa +: Sequent() :+ pfa )
    }

    "apply correctly to a proof with quantifiers with overbinding" in {
      import proof2._
      val p_s = applySubstitution( subst2 )( proof )
      val pfa = All( y, P( y, x ) )
      p_s.endSequent must beMultiSetEqual( pfa +: Sequent() :+ pfa )
    }

  }
}
