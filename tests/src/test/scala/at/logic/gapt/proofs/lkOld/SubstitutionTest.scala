
package at.logic.gapt.proofs.lkOld

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lkOld.base._
import org.specs2.mutable._

class SubstitutionTest extends Specification {
  "Substitutions" should {
    object proof1 {
      val x = Var( "x", Ti )
      val p = Const( "P", Ti -> To )
      val px = HOLAtom( p, x :: Nil )
      val ax1 = Axiom( px :: Nil, px :: Nil )
      val ax2 = Axiom( px :: Nil, px :: Nil )
      val proof = CutRule( ax1, ax2, ax1.root.succedent.toList.head, ax2.root.antecedent.toList.head )
      val a = Const( "a", Ti )
      val f = Const( "f", Ti -> Ti )
      val fa = App( f, a )
      val subst = Substitution( x, fa )
    }

    object proof2 {
      val x = Var( "x", Ti )
      val y = Var( "y", Ti )
      val p = Const( "P", Ti -> ( Ti -> To ) )
      val pxy = HOLAtom( p, List( x, y ) )
      val allxpx = All( x, pxy )
      val ax1 = Axiom( pxy :: Nil, pxy :: Nil )
      val r1 = ForallLeftRule( ax1, ax1.root.antecedent( 0 ), allxpx, x )
      val proof = ForallRightRule( r1, r1.root.succedent( 0 ), allxpx, x )

      val a = Const( "a", Ti )
      val f = Const( "f", Ti -> Ti )
      val fa = App( f, a )
      val subst = Substitution( y, fa )
      val subst2 = Substitution( y, x ) //test for overbinding
    }

    "apply correctly to a simple proof" in {
      val p_s = applySubstitution( proof1.proof, proof1.subst )
      val pfa = HOLAtom( proof1.p, proof1.fa :: Nil )
      val new_seq = HOLSequent( pfa :: Nil, pfa :: Nil )
      val seq = p_s._1.root.toHOLSequent
      seq must beEqualTo( new_seq )
    }

    "apply correctly to a proof with quantifiers" in {
      val p_s = applySubstitution( proof2.proof, proof2.subst )
      val pfa = All( proof2.x, HOLAtom( proof2.p, List( proof2.x, proof2.fa ) ) )
      val new_seq = HOLSequent( pfa :: Nil, pfa :: Nil )
      val seq = p_s._1.root.toHOLSequent
      seq must beEqualTo( new_seq )
    }

  }
}
