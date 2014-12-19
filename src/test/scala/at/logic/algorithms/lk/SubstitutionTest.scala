
package at.logic.algorithms.lk

import at.logic.language.hol._
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk._
import at.logic.language.lambda.types._

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class SubstitutionTest extends SpecificationWithJUnit {
  "Substitutions" should {
    object proof1 {
      val x = HOLVar( "x", Ti )
      val p = HOLConst("P", Ti -> To)
      val px = Atom(p, x::Nil )
      val ax1 = Axiom( px::Nil, px::Nil )
      val ax2 = Axiom( px::Nil, px::Nil )
      val proof = CutRule( ax1, ax2, ax1.root.succedent.toList.head, ax2.root.antecedent.toList.head )
      val a = HOLConst("a", Ti)
      val f = HOLConst("f", Ti -> Ti)
      val fa = HOLApp(f, a)
      val subst = Substitution( x, fa )
    }

    object proof2 {
      val x = HOLVar( "x", Ti )
      val y = HOLVar( "y", Ti )
      val p = HOLConst("P", Ti -> (Ti -> To))
      val pxy = Atom(p, List(x,y))
      val allxpx = AllVar(x,pxy)
      val ax1 = Axiom( pxy::Nil, pxy::Nil )
      val r1 = ForallLeftRule(ax1, ax1.root.antecedent(0), allxpx, x )
      val proof = ForallRightRule(r1, r1.root.succedent(0), allxpx, x)

      val a = HOLConst("a", Ti)
      val f = HOLConst("f", Ti -> Ti)
      val fa = HOLApp(f, a)
      val subst = Substitution( y, fa )
      val subst2 = Substitution( y, x ) //test for overbinding
    }

    "apply correctly to a simple proof" in {
      val p_s = applySubstitution( proof1.proof, proof1.subst )
      val pfa = Atom(proof1.p, proof1.fa::Nil )
      val new_seq = FSequent( pfa::Nil, pfa::Nil )
      val seq = p_s._1.root.toFSequent
      seq must beEqualTo( new_seq )
    }

    "apply correctly to a proof with quantifiers" in {
      val p_s = applySubstitution( proof2.proof, proof2.subst )
      val pfa = AllVar(proof2.x, Atom(proof2.p, List(proof2.x, proof2.fa) ))
      val new_seq = FSequent( pfa::Nil, pfa::Nil )
      val seq = p_s._1.root.toFSequent
      seq must beEqualTo( new_seq )
    }

  }
}
