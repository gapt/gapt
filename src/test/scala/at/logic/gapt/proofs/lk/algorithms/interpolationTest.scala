package at.logic.gapt.proofs.lk.algorithms

import at.logic.gapt.language.lambda.types._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.occurrences._
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import at.logic.gapt.language.fol._
import at.logic.gapt.language.lambda.types._
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.lk._

@RunWith( classOf[JUnitRunner] )
class interpolationTest extends SpecificationWithJUnit {
  "interpolation" should {

    "correctly interpolate an axiom with top" in {
      val p = FOLAtom( "p", Nil )
      val ax = Axiom( p :: Nil, p :: Nil )
      val npart = Set[FormulaOccurrence]()
      val ppart = Set( ax.root.antecedent( 0 ), ax.root.succedent( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )

      ipl must beEqualTo( FOLTopC )
    }

    "correctly create an interpolating proof" in {
      val p = FOLAtom( "p", Nil )
      val ax = Axiom( p :: Nil, p :: Nil )
      val npart = Set( ax.root.antecedent( 0 ), ax.root.succedent( 0 ) )
      val ppart = Set[FormulaOccurrence]()
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )

      ipl must beEqualTo( FOLBottomC )
      nproof.root.toFSequent must beEqualTo( FSequent( p :: Nil, p :: FOLBottomC :: Nil ) )
      pproof.root.toFSequent must beEqualTo( FSequent( FOLBottomC :: Nil, Nil ) )
    }

    "correctly interpolate a single unary inference with not p" in {
      val p = FOLAtom( "p", Nil )
      val q = FOLAtom( "q", Nil )
      val ax = Axiom( p :: Nil, p :: Nil )
      val pr = OrRight1Rule( ax, p, q )
      val npart = Set( pr.root.succedent( 0 ) )
      val ppart = Set( pr.root.antecedent( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( pr, npart, ppart )

      ipl must beEqualTo( FOLNeg( p ) )
      nproof.root.toFSequent must beEqualTo( FSequent( Nil, FOLNeg( p ) :: FOLOr( p, q ) :: Nil ) )
      pproof.root.toFSequent must beEqualTo( FSequent( p :: FOLNeg( p ) :: Nil, Nil ) )
    }

    "correctly interpolate a single binary inference with bot or q" in {
      val p = FOLAtom( "p", Nil )
      val q = FOLAtom( "q", Nil )
      val axp = Axiom( p :: Nil, p :: Nil )
      val axq = Axiom( q :: Nil, q :: Nil )
      val pr = OrLeftRule( axp, axq, p, q )
      val npart = Set( pr.root.antecedent( 0 ), pr.root.succedent( 0 ) )
      val ppart = Set( pr.root.succedent( 1 ) )
      val ( nproof, pproof, ipl ) = Interpolate( pr, npart, ppart )

      ipl must beEqualTo( FOLOr( FOLBottomC, q ) )
      nproof.root.toFSequent must beEqualTo( FSequent( FOLOr( p, q ) :: Nil, p :: FOLOr( FOLBottomC, q ) :: Nil ) )
      pproof.root.toFSequent must beEqualTo( FSequent( FOLOr( FOLBottomC, q ) :: Nil, q :: Nil ) )
    }

    "correctly interpolate a small proof of 4 inference rules" in {
      val p = FOLAtom( "p", Nil )
      val q = FOLAtom( "q", Nil )
      val r = FOLAtom( "r", Nil )

      val axp = Axiom( p :: Nil, p :: Nil )
      val axq = Axiom( q :: Nil, q :: Nil )
      val axr = Axiom( r :: Nil, r :: Nil )
      val p1 = NegLeftRule( axq, q )
      val p2 = OrLeftRule( p1, axr, q, r )
      val p3 = ImpRightRule( p2, FOLNeg( q ), r )
      val p4 = ImpLeftRule( axp, p3, p, FOLOr( q, r ) )

      val npart = Set( p4.root.antecedent( 0 ), p4.root.antecedent( 1 ) )
      val ppart = Set( p4.root.succedent( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( p4, npart, ppart )

      ipl must beEqualTo( FOLOr( FOLBottomC, FOLOr( q, r ) ) )
      nproof.root.toFSequent must beEqualTo( FSequent( p :: FOLImp( p, FOLOr( q, r ) ) :: Nil, FOLOr( FOLBottomC, FOLOr( q, r ) ) :: Nil ) )
      pproof.root.toFSequent must beEqualTo( FSequent( FOLOr( FOLBottomC, FOLOr( q, r ) ) :: Nil, FOLImp( FOLNeg( q ), r ) :: Nil ) )
    }

  }
}
