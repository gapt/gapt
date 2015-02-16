
package at.logic.proofs.lk.algorithms

import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.proofs.lk._
import at.logic.proofs.lk.base._
import at.logic.proofs.occurrences._
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class interpolationTest extends SpecificationWithJUnit {
  "interpolation" should {

    "correctly interpolate an axiom with top" in {
      val p = HOLAtom(HOLConst("p", To))
      val ax = Axiom( p::Nil, p::Nil )
      val npart = Set[FormulaOccurrence]()
      val ppart = Set( ax.root.antecedent(0), ax.root.succedent(0) )
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )

      ipl must beEqualTo( TopC )
    }

    "correctly create an interpolating proof" in {
      val p = HOLAtom(HOLConst("p", To))
      val ax = Axiom( p::Nil, p::Nil )
      val npart = Set( ax.root.antecedent(0), ax.root.succedent(0) )
      val ppart = Set[FormulaOccurrence]()
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )

      ipl must beEqualTo( BottomC )
      nproof.root.toFSequent must beEqualTo ( FSequent( p::Nil, p::BottomC::Nil ) )
      pproof.root.toFSequent must beEqualTo ( FSequent( BottomC::Nil, Nil ) )
    }

    "correctly interpolate a single unary inference with not p" in {
      val p = HOLAtom(HOLConst("p", To))
      val q = HOLAtom(HOLConst("q", To))
      val ax = Axiom( p::Nil, p::Nil )
      val pr = OrRight1Rule( ax, p, q )
      val npart = Set( pr.root.succedent( 0 ) )
      val ppart = Set( pr.root.antecedent( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( pr, npart, ppart )

      ipl must beEqualTo( HOLNeg( p ) )
      nproof.root.toFSequent must beEqualTo ( FSequent( Nil, HOLNeg( p )::HOLOr( p, q )::Nil ) )
      pproof.root.toFSequent must beEqualTo ( FSequent( p::HOLNeg( p )::Nil, Nil ) )
    }

    "correctly interpolate a single binary inference with bot or q" in {
      val p = HOLAtom(HOLConst("p", To))
      val q = HOLAtom(HOLConst("q", To))
      val axp = Axiom( p::Nil, p::Nil )
      val axq = Axiom( q::Nil, q::Nil )
      val pr = OrLeftRule( axp, axq, p, q )
      val npart = Set( pr.root.antecedent( 0 ), pr.root.succedent( 0 ) )
      val ppart = Set( pr.root.succedent( 1 ) )
      val ( nproof, pproof, ipl ) = Interpolate( pr, npart, ppart )

      ipl must beEqualTo( HOLOr( BottomC, q ) )
      nproof.root.toFSequent must beEqualTo ( FSequent( HOLOr( p, q )::Nil, p::HOLOr( BottomC, q )::Nil ) )
      pproof.root.toFSequent must beEqualTo ( FSequent( HOLOr( BottomC, q )::Nil, q::Nil ) )
    }

    "correctly interpolate a small proof of 4 inference rules" in {
      val p = HOLAtom(HOLConst("p", To))
      val q = HOLAtom(HOLConst("q", To))
      val r = HOLAtom(HOLConst("r", To))

      val axp = Axiom( p::Nil, p::Nil )
      val axq = Axiom( q::Nil, q::Nil )
      val axr = Axiom( r::Nil, r::Nil )
      val p1 = NegLeftRule( axq, q )
      val p2 = OrLeftRule( p1, axr, q, r )
      val p3 = ImpRightRule( p2, HOLNeg( q ), r )
      val p4 = ImpLeftRule( axp, p3, p, HOLOr( q, r ) )

      val npart = Set( p4.root.antecedent( 0 ), p4.root.antecedent( 1 ) )
      val ppart = Set( p4.root.succedent( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( p4, npart, ppart )

      ipl must beEqualTo( HOLOr( BottomC, HOLOr( q, r ) ) )
      nproof.root.toFSequent must beEqualTo ( FSequent( p::HOLImp( p, HOLOr( q, r ))::Nil, HOLOr( BottomC, HOLOr( q, r ) )::Nil ) )
      pproof.root.toFSequent must beEqualTo ( FSequent( HOLOr( BottomC, HOLOr( q, r ) )::Nil, HOLImp( HOLNeg( q ), r )::Nil ) )
    }


  }
}
