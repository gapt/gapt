package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk.base._
import org.specs2.execute.Success
import org.specs2.mutable._
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.formats.prover9.Prover9TermParser.parseFormula
import at.logic.gapt.provers.eqProver.EquationalProver

class LKNewInterpolationTest extends Specification {
  "applyInterpolation" should {

    "correctly interpolate a logical axiom with top" in {
      val p = FOLAtom( "p", Nil )
      val ax = LogicalAxiom( p )
      val npart = Seq[SequentIndex]()
      val ppart = ax.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )
      val I = ExtractInterpolant( ax, npart, ppart )

      ipl must beEqualTo( Top() )
      I must beEqualTo( ipl )
      success
    }

    "correctly interpolate a logical axiom with bottom" in {
      val p = FOLAtom( "p", Nil )
      val ax = LogicalAxiom( p )
      val ppart = Seq[SequentIndex]()
      val npart = ax.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )
      val I = ExtractInterpolant( ax, npart, ppart )

      ipl must beEqualTo( Bottom() )
      I must beEqualTo( ipl )
      success
    }

    "correctly interpolate a logical axiom with the atom of the axiom itself" in {
      val p = FOLAtom( "p", Nil )
      val ax = LogicalAxiom( p )
      val npart = ax.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = ax.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )
      val I = ExtractInterpolant( ax, npart, ppart )

      ipl must beEqualTo( p )
      I must beEqualTo( ipl )
      success
    }

    "correctly interpolate a logical axiom with the negated atom of the axiom itself" in {
      val p = FOLAtom( "p", Nil )
      val ax = LogicalAxiom( p )
      val ppart = ax.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val npart = ax.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )
      val I = ExtractInterpolant( ax, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      I must beEqualTo( ipl )
      success
    }

    "correctly interpolate a TopAxiom with bottom" in {
      val npart = TopAxiom.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( TopAxiom, npart, ppart )
      val I = ExtractInterpolant( TopAxiom, npart, ppart )

      ipl must beEqualTo( Bottom() )
      I must beEqualTo( ipl )
      success
    }

    "correctly interpolate a TopAxiom with top" in {
      val ppart = TopAxiom.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val npart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( TopAxiom, npart, ppart )
      val I = ExtractInterpolant( TopAxiom, npart, ppart )

      ipl must beEqualTo( Top() )
      I must beEqualTo( ipl )
      success
    }

    "correctly interpolate a BottomAxiom with bottom" in {
      val npart = BottomAxiom.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( BottomAxiom, npart, ppart )
      val I = ExtractInterpolant( BottomAxiom, npart, ppart )

      ipl must beEqualTo( Bottom() )
      I must beEqualTo( ipl )
      success
    }

    "correctly interpolate a BottomAxiom with top" in {
      val ppart = BottomAxiom.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val npart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( BottomAxiom, npart, ppart )
      val I = ExtractInterpolant( BottomAxiom, npart, ppart )

      ipl must beEqualTo( Top() )
      I must beEqualTo( ipl )
      success
    }

    "correctly interpolate a ReflexivityAxiom with bottom" in {
      val c = FOLConst( "c" )
      val ax = ReflexivityAxiom( c )
      val npart = ax.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )
      val I = ExtractInterpolant( ax, npart, ppart )

      ipl must beEqualTo( Bottom() )
      I must beEqualTo( ipl )
      success
    }

    "correctly interpolate a ReflexivityAxiom with top" in {
      val c = FOLConst( "c" )
      val ax = ReflexivityAxiom( c )
      val ppart = ax.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val npart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )
      val I = ExtractInterpolant( ax, npart, ppart )

      ipl must beEqualTo( Top() )
      I must beEqualTo( ipl )
      success
    }
  }
}
