package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
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

    val p = FOLAtom( "p", Nil )
    val q = FOLAtom( "q", Nil )
    val ax = LogicalAxiom( p )
    val ax2 = LogicalAxiom( q )

    "correctly create a proof containing WeakeningLeft with Bottom" in {
      val proof = WeakeningLeftRule( ax, q )
      val npart = proof.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( q :: p :: Nil, p :: Bottom() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing WeakeningLeft (different partition) with p" in {
      val proof = WeakeningLeftRule( ax, q )
      val npart = proof.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( p )
      nproof.endSequent must beEqualTo( HOLSequent( q :: p :: Nil, p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Nil ) )
      success
    }

    "correctly create a proof containing WeakeningLeft (with yet another partition) with Neg( p )" in {
      val proof = WeakeningLeftRule( ax, q )
      val npart = proof.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, p :: Neg( p ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( q :: Neg( p ) :: p :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing WeakeningLeft (and another partition) with Top" in {
      val proof = WeakeningLeftRule( ax, q )
      val npart = Seq[SequentIndex]()
      val ppart = proof.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( q :: Top() :: p :: Nil, p :: Nil ) )
      success
    }

    "correctly create a proof containing WeakeningRight with Bottom" in {
      val proof = WeakeningRightRule( ax, q )
      val npart = proof.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Bottom() :: q :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing WeakeningRight (different partition) with p" in {
      val proof = WeakeningRightRule( ax, q )
      val npart = proof.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( p )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: q :: Nil ) )
      success
    }

    "correctly create a proof containing WeakeningRight (with yet another partition) with Neg( p )" in {
      val proof = WeakeningRightRule( ax, q )
      val npart = proof.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, p :: Neg( p ) :: q :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Neg( p ) :: p :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing WeakeningRight (and another partition) with Top" in {
      val proof = WeakeningRightRule( ax, q )
      val npart = Seq[SequentIndex]()
      val ppart = proof.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Top() :: p :: Nil, p :: q :: Nil ) )
      success
    }

    "correctly create a proof containing ContractionLeft with Bottom" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = ContractionLeftRule( proof, p )
      val npart = proof1.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Bottom() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing ContractionLeft (different partition) with p" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = ContractionLeftRule( proof, p )
      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( p )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Nil ) )
      success
    }

    "correctly create a proof containing ContractionLeft (with yet another partition) with Neg( p )" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = ContractionLeftRule( proof, p )
      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, p :: Neg( p ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( p :: Neg( p ) :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing ContractionLeft (and another partition) with Top" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = ContractionLeftRule( proof, p )
      val npart = Seq[SequentIndex]()
      val ppart = proof1.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( p :: Top() :: Nil, p :: Nil ) )
      success
    }

    "correctly create a proof containing ContractionRight with Bottom" in {
      val proof = WeakeningRightRule( ax, p )
      val proof1 = ContractionRightRule( proof, p )
      val npart = proof1.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, Bottom() :: p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing ContractionRight (different partition) with p" in {
      val proof = WeakeningRightRule( ax, p )
      val proof1 = ContractionRightRule( proof, p )
      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( p )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Nil ) )
      success
    }

    "correctly create a proof containing ContractionRight (with yet another partition) with Neg( p )" in {
      val proof = WeakeningRightRule( ax, p )
      val proof1 = ContractionRightRule( proof, p )
      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Neg( p ) :: p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Neg( p ) :: p :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing ContractionRight (and another partition) with Top" in {
      val proof = WeakeningRightRule( ax, p )
      val proof1 = ContractionRightRule( proof, p )
      val npart = Seq[SequentIndex]()
      val ppart = proof1.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Top() :: p :: Nil, p :: Nil ) )
      success
    }

    "correctly create a proof containing NegationLeft with Bottom" in {
      val proof = WeakeningRightRule( ax, p )
      val proof1 = NegLeftRule( proof, p )
      val npart = proof1.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( Neg( p ) :: p :: Nil, Bottom() :: p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing NegationLeft (different partition) with Bottom" in {
      val proof = WeakeningRightRule( ax, p )
      val proof1 = NegLeftRule( proof, p )
      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( Neg( p ) :: p :: Nil, Bottom() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, p :: Nil ) )
      success
    }

    "correctly create a proof containing NegationLeft (with yet another partition) with Top" in {
      val proof = WeakeningRightRule( ax, p )
      val proof1 = NegLeftRule( proof, p )
      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Neg( p ) :: Top() :: p :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing NegationLeft (and another partition) with Top" in {
      val proof = WeakeningRightRule( ax, p )
      val proof1 = NegLeftRule( proof, p )
      val npart = Seq[SequentIndex]()
      val ppart = proof1.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Neg( p ) :: Top() :: p :: Nil, p :: Nil ) )
      success
    }

    "correctly create a proof containing NegationRight with Bottom" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = NegRightRule( proof, p )
      val npart = proof1.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Bottom() :: Neg( p ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing NegationRight (different partition) with p" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = NegRightRule( proof, p )
      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( p )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Neg( p ) :: Nil ) )
      success
    }

    "correctly create a proof containing NegationRight (with yet another partition) with Neg( p )" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = NegRightRule( proof, p )
      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, p :: Neg( p ) :: Neg( p ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Neg( p ) :: p :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing NegationRight (and another partition) with Top" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = NegRightRule( proof, p )
      val npart = Seq[SequentIndex]()
      val ppart = proof1.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Top() :: p :: Nil, p :: Neg( p ) :: Nil ) )
      success
    }

    "correctly create a proof containing AndLeft with Bottom" in {
      val proof = WeakeningRightRule( ax, q )
      val proof1 = WeakeningLeftRule( proof, q )
      val proof2 = AndLeftRule( proof1, p, q )
      val npart = proof2.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof2, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( And( p, q ) :: Nil, p :: Bottom() :: q :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing AndLeft (different partition) with p" in {
      val proof = WeakeningRightRule( ax, q )
      val proof1 = WeakeningLeftRule( proof, q )
      val proof2 = AndLeftRule( proof1, p, q )
      val npart = proof2.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof2.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof2, npart, ppart )

      ipl must beEqualTo( p )
      nproof.endSequent must beEqualTo( HOLSequent( And( p, q ) :: Nil, p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: q :: Nil ) )
      success
    }

    "correctly create a proof containing AndLeft (yet another partition) with Neg( p )" in {
      val proof = WeakeningRightRule( ax, q )
      val proof1 = WeakeningLeftRule( proof, q )
      val proof2 = AndLeftRule( proof1, p, q )
      val npart = proof2.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof2.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof2, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, p :: Neg( p ) :: q :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( p, q ) :: Neg( p ) :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing AndLeft (and another partition) with Top" in {
      val proof = WeakeningRightRule( ax, q )
      val proof1 = WeakeningLeftRule( proof, q )
      val proof2 = AndLeftRule( proof1, p, q )
      val npart = Seq[SequentIndex]()
      val ppart = proof2.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof2, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( p, q ) :: Top() :: Nil, p :: q :: Nil ) )
      success
    }

    "correctly create a proof containing OrRight with Bottom" in {
      val proof = WeakeningRightRule( ax, q )
      val proof1 = WeakeningLeftRule( proof, q )
      val proof2 = OrRightRule( proof1, p, q )
      val npart = proof2.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof2, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( q :: p :: Nil, Bottom() :: Or( p, q ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing OrRight (different partition) with p" in {
      val proof = WeakeningRightRule( ax, q )
      val proof1 = WeakeningLeftRule( proof, q )
      val proof2 = OrRightRule( proof1, p, q )
      val npart = proof2.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof2.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof2, npart, ppart )

      ipl must beEqualTo( p )
      nproof.endSequent must beEqualTo( HOLSequent( q :: p :: Nil, p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( p :: Nil, Or( p, q ) :: Nil ) )
      success
    }

    "correctly create a proof containing OrRight (yet another partition) with Neg( p )" in {
      val proof = WeakeningRightRule( ax, q )
      val proof1 = WeakeningLeftRule( proof, q )
      val proof2 = OrRightRule( proof1, p, q )
      val npart = proof2.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof2.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof2, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Neg( p ) :: Or( p, q ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( q :: Neg( p ) :: p :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing OrRight (and another partition) with Top" in {
      val proof = WeakeningRightRule( ax, q )
      val proof1 = WeakeningLeftRule( proof, q )
      val proof2 = OrRightRule( proof1, p, q )
      val npart = Seq[SequentIndex]()
      val ppart = proof2.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof2, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( q :: Top() :: p :: Nil, Or( p, q ) :: Nil ) )
      success
    }

    "correctly create a proof containing ImpRight with Bottom" in {
      val proof = WeakeningLeftRule( ax, q )
      val proof1 = ImpRightRule( proof, q, p )
      val npart = proof1.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, Bottom() :: Imp( q, p ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing ImpRight (different partition) with p" in {
      val proof = WeakeningLeftRule( ax, q )
      val proof1 = ImpRightRule( proof, q, p )
      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( p )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( p :: Nil, Imp( q, p ) :: Nil ) )
      success
    }

    "correctly create a proof containing ImpRight (yet another partition) Neg( p )" in {
      val proof = WeakeningLeftRule( ax, q )
      val proof1 = ImpRightRule( proof, q, p )
      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Neg( p ) :: Imp( q, p ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Neg( p ) :: p :: Nil, Nil ) )
      success
    }

    "correctly create a proof containing ImpRight (and another partition) with Top" in {
      val proof = WeakeningLeftRule( ax, q )
      val proof1 = ImpRightRule( proof, q, p )
      val npart = Seq[SequentIndex]()
      val ppart = proof1.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Top() :: p :: Nil, Imp( q, p ) :: Nil ) )
      success
    }

    "correctly interpolate a single unary inference with not p with Neg( p )" in {
      val proof = WeakeningRightRule( ax, q )
      val proof1 = OrRightRule( proof, p, q )
      val npart = Seq( Suc( 0 ) )
      val ppart = Seq( Ant( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, Neg( p ) :: Or( p, q ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Neg( p ) :: p :: Nil, Nil ) )
    }

    "correctly interpolate a proof containing OrLeftRule with (Bottom ∨ Bottom)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = OrLeftRule( proof3, p, ax2, q )
      val npart = proof4.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Bottom(), Bottom() ) )
      nproof.endSequent must beEqualTo( HOLSequent( Or( p, q ) :: Nil, p :: q :: Or( Bottom(), Bottom() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), Bottom() ) :: Nil, Nil ) )
      success
    }

    "correctly interpolate a proof containing OrLeftRule (different partition) with (p ∨ q)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = OrLeftRule( proof3, p, ax2, q )
      val npart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( p, q ) )
      nproof.endSequent must beEqualTo( HOLSequent( Or( p, q ) :: Nil, Or( p, q ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( p, q ) :: Nil, p :: q :: Nil ) )
      success
    }

    "correctly interpolate a proof containing OrLeftRule (yet another partition) with (Neg( p ) ∧ Neg( q ))" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = OrLeftRule( proof3, p, ax2, q )
      val npart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( Neg( p ), Neg( q ) ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, p :: q :: And( Neg( p ), Neg( q ) ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( Neg( p ), Neg( q ) ) :: Or( p, q ) :: Nil, Nil ) )
      success
    }

    "correctly interpolate a proof containing OrLeftRule (and another partition) with (Top ∧ Top)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = OrLeftRule( proof3, p, ax2, q )
      val npart = Seq[SequentIndex]()
      val ppart = proof4.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( Top(), Top() ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, And( Top(), Top() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( Top(), Top() ) :: Or( p, q ) :: Nil, p :: q :: Nil ) )
      success
    }

    "correctly interpolate a proof containing OrLeftRule (and again another partition) with (Bottom ∨ q)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = OrLeftRule( proof3, p, ax2, q )
      val npart = Seq( Ant( 0 ), Suc( 0 ) )
      val ppart = Seq( Suc( 1 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Bottom(), q ) )
      nproof.endSequent must beEqualTo( HOLSequent( Or( p, q ) :: Nil, p :: Or( Bottom(), q ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), q ) :: Nil, q :: Nil ) )
      success
    }

    "correctly interpolate a proof containing OrLeftRule (and again and again...) with (Top ∧ Neg( q ))" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = OrLeftRule( proof3, p, ax2, q )
      val npart = Seq( Suc( 1 ) )
      val ppart = Seq( Ant( 0 ), Suc( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( Top(), Neg( q ) ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, q :: And( Top(), Neg( q ) ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( Top(), Neg( q ) ) :: Or( p, q ) :: Nil, p :: Nil ) )
      success
    }

    "correctly interpolate a proof containing OrLeftRule (and again and again...) with (Neg( p ) ∧ Top)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = OrLeftRule( proof3, p, ax2, q )
      val npart = Seq( Suc( 0 ) )
      val ppart = Seq( Ant( 0 ), Suc( 1 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( Neg( p ), Top() ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, p :: And( Neg( p ), Top() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( Neg( p ), Top() ) :: Or( p, q ) :: Nil, q :: Nil ) )
      success
    }

    "correctly interpolate a proof containing OrLeftRule (and again and again...) with (p ∨ Bottom)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = OrLeftRule( proof3, p, ax2, q )
      val npart = Seq( Ant( 0 ), Suc( 1 ) )
      val ppart = Seq( Suc( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( p, Bottom() ) )
      nproof.endSequent must beEqualTo( HOLSequent( Or( p, q ) :: Nil, q :: Or( p, Bottom() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( p, Bottom() ) :: Nil, p :: Nil ) )
      success
    }

    "correctly interpolate a proof containing AndRightRule with (Bottom ∨ Bottom)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = AndRightRule( proof3, p, ax2, q )
      val npart = proof4.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Bottom(), Bottom() ) )
      nproof.endSequent must beEqualTo( HOLSequent( p :: q :: Nil, And( p, q ) :: Or( Bottom(), Bottom() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), Bottom() ) :: Nil, Nil ) )
      success
    }

    "correctly interpolate a proof containing AndRightRule (different partition) with (p ∧ q)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = AndRightRule( proof3, p, ax2, q )
      val npart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( p, q ) )
      nproof.endSequent must beEqualTo( HOLSequent( p :: q :: Nil, And( p, q ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( p, q ) :: Nil, And( p, q ) :: Nil ) )
      success
    }

    "correctly interpolate a proof containing AndRightRule (yet another partition) with (Neg( p ) ∧ Neg( q ))" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = AndRightRule( proof3, p, ax2, q )
      val npart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Neg( p ), Neg( q ) ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, And( p, q ) :: Or( Neg( p ), Neg( q ) ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Neg( p ), Neg( q ) ) :: p :: q :: Nil, Nil ) )
      success
    }

    "correctly interpolate a proof containing AndRightRule (and another partition) with (Top ∧ Top)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = AndRightRule( proof3, p, ax2, q )
      val npart = Seq[SequentIndex]()
      val ppart = proof4.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( Top(), Top() ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, And( Top(), Top() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( Top(), Top() ) :: p :: q :: Nil, And( p, q ) :: Nil ) )
      success
    }

    "correctly interpolate a proof containing AndRightRule (and again another partition) with (Neg( p ) ∨ Bottom)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = AndRightRule( proof3, p, ax2, q )
      val npart = Seq( Ant( 1 ), Suc( 0 ) )
      val ppart = Seq( Ant( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Neg( p ), Bottom() ) )
      nproof.endSequent must beEqualTo( HOLSequent( q :: Nil, And( p, q ) :: Or( Neg( p ), Bottom() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Neg( p ), Bottom() ) :: p :: Nil, Nil ) )
      success
    }

    "correctly interpolate a proof containing AndRightRule (and again and again...) with (Top ∧ q)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = AndRightRule( proof3, p, ax2, q )
      val npart = Seq( Ant( 1 ) )
      val ppart = Seq( Ant( 0 ), Suc( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( Top(), q ) )
      nproof.endSequent must beEqualTo( HOLSequent( q :: Nil, And( Top(), q ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( Top(), q ) :: p :: Nil, And( p, q ) :: Nil ) )
      success
    }

    "correctly interpolate a proof containing AndRightRule (and again and again...) with (p ∧ Top)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = AndRightRule( proof3, p, ax2, q )
      val npart = Seq( Ant( 0 ) )
      val ppart = Seq( Ant( 1 ), Suc( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( p, Top() ) )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, And( p, Top() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( p, Top() ) :: q :: Nil, And( p, q ) :: Nil ) )
      success
    }

    "correctly interpolate a proof containing AndRightRule (and again and again...) with (Bottom ∨ Neg( q ))" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = AndRightRule( proof3, p, ax2, q )
      val npart = Seq( Ant( 0 ), Suc( 0 ) )
      val ppart = Seq( Ant( 1 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Bottom(), Neg( q ) ) )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, And( p, q ) :: Or( Bottom(), Neg( q ) ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), Neg( q ) ) :: q :: Nil, Nil ) )
      success
    }

    "correctly interpolate a proof containing ImpLeftRule with (Bottom ∨ Bottom)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = ImpLeftRule( proof3, p, ax2, q )
      val npart = proof4.endSequent.indices
      val ppart = Seq[SequentIndex]()
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Bottom(), Bottom() ) )
      nproof.endSequent must beEqualTo( HOLSequent( Imp( p, q ) :: p :: Nil, q :: Or( Bottom(), Bottom() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), Bottom() ) :: Nil, Nil ) )
      success
    }

    "correctly interpolate a proof containing ImpLeftRule (different partition) with (Bottom ∨ q)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = ImpLeftRule( proof3, p, ax2, q )
      val npart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Bottom(), q ) )
      nproof.endSequent must beEqualTo( HOLSequent( Imp( p, q ) :: p :: Nil, Or( Bottom(), q ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), q ) :: Nil, q :: Nil ) )
      success
    }

    "correctly interpolate a proof containing ImpLefttRule (yet another partition) with (Top ∧ Neg( q ))" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = ImpLeftRule( proof3, p, ax2, q )
      val npart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof4.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( Top(), Neg( q ) ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, q :: And( Top(), Neg( q ) ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( Top(), Neg( q ) ) :: Imp( p, q ) :: p :: Nil, Nil ) )
      success
    }

    "correctly interpolate a proof containing ImpLeftRule (and another partition) with (Top ∧ Top)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = ImpLeftRule( proof3, p, ax2, q )
      val npart = Seq[SequentIndex]()
      val ppart = proof4.endSequent.indices
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( Top(), Top() ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, And( Top(), Top() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( Top(), Top() ) :: Imp( p, q ) :: p :: Nil, q :: Nil ) )
      success
    }

    "correctly interpolate a proof containing ImpLeftRule (and again another partition) with (p ∧ Neg( q ))" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = ImpLeftRule( proof3, p, ax2, q )
      val npart = Seq( Ant( 1 ), Suc( 0 ) )
      val ppart = Seq( Ant( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( p, Neg( q ) ) )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, q :: And( p, Neg( q ) ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( p, Neg( q ) ) :: Imp( p, q ) :: Nil, Nil ) )
      success
    }

    "correctly interpolate a proof containing ImpLeftRule (and again and again...) with (p ∧ Top)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = ImpLeftRule( proof3, p, ax2, q )
      val npart = Seq( Ant( 1 ) )
      val ppart = Seq( Ant( 0 ), Suc( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( And( p, Top() ) )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, And( p, Top() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( And( p, Top() ) :: Imp( p, q ) :: Nil, q :: Nil ) )
      success
    }

    "correctly interpolate a proof containing ImpLeftRule (and again and again...) with (Neg( p ) ∨ q)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = ImpLeftRule( proof3, p, ax2, q )
      val npart = Seq( Ant( 0 ) )
      val ppart = Seq( Ant( 1 ), Suc( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Neg( p ), q ) )
      nproof.endSequent must beEqualTo( HOLSequent( Imp( p, q ) :: Nil, Or( Neg( p ), q ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Neg( p ), q ) :: p :: Nil, q :: Nil ) )
      success
    }

    "correctly interpolate a proof containing ImpLeftRule (and again and again...) with (Neg( p ) ∨ Bottom)" in {
      val proof = WeakeningLeftRule( ax, p )
      val proof1 = WeakeningRightRule( ax2, q )
      val proof2 = ContractionRightRule( proof1, q )
      val proof3 = ContractionLeftRule( proof, p )
      val proof4 = ImpLeftRule( proof3, p, ax2, q )
      val npart = Seq( Ant( 0 ), Suc( 0 ) )
      val ppart = Seq( Ant( 1 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Neg( p ), Bottom() ) )
      nproof.endSequent must beEqualTo( HOLSequent( Imp( p, q ) :: Nil, q :: Or( Neg( p ), Bottom() ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Neg( p ), Bottom() ) :: p :: Nil, Nil ) )
      success
    }

    "correctly interpolate a small proof with 4 inference rules" in {
      val r = FOLAtom( "r", Nil )
      val axr = LogicalAxiom( r )
      val proof1 = NegLeftRule( ax2, q )
      val proof2 = OrLeftRule( proof1, q, axr, r )
      val proof3 = ImpRightRule( proof2, Neg( q ), r )
      val proof4 = ImpLeftRule( ax, p, proof3, Or( q, r ) )

      val npart = Seq( Ant( 0 ), Ant( 1 ) )
      val ppart = Seq( Suc( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( proof4, npart, ppart )

      ipl must beEqualTo( Or( Bottom(), Or( q, r ) ) )
      nproof.endSequent must beEqualTo( HOLSequent( Imp( p, Or( q, r ) ) :: p :: Nil, Or( Bottom(), Or( q, r ) ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), Or( q, r ) ) :: Nil, Imp( Neg( q ), r ) :: Nil ) )
    }

    "correctly interpolate a proof containing EqualityLeft with Bottom" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityLeftRule( proof, aeqb, Ant( 1 ), pb )

      val npart = proof1.endSequent.indices
      val ppart = Seq.empty[SequentIndex]

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( pb :: aeqb :: Nil, pa :: ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Nil ) )
    }

    "correctly interpolate a proof containing EqualityLeft with Top" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityLeftRule( proof, aeqb, Ant( 1 ), pb )

      val npart = Seq.empty[SequentIndex]
      val ppart = proof1.endSequent.indices

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( pb :: aeqb :: ipl :: Nil, pa :: Nil ) )
    }

    "correctly interpolate a proof containing EqualityLeft with P(a)" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityLeftRule( proof, aeqb, Ant( 1 ), pb )

      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( pa )
      nproof.endSequent must beEqualTo( HOLSequent( pb :: aeqb :: Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, pa :: Nil ) )
    }

    "correctly interpolate a proof containing EqualityLeft with Neg( P(a) )" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityLeftRule( proof, aeqb, Ant( 1 ), pb )

      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Neg( pa ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, pa :: ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( pb :: aeqb :: ipl :: Nil, Nil ) )
    }

    "correctly interpolate a proof containing EqualityLeft with a=b → P(a)" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityLeftRule( proof, aeqb, Ant( 1 ), pb )

      val npart = Seq( Ant( 0 ) )
      val ppart = Seq( Ant( 1 ), Suc( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Imp( aeqb, pa ) )
      nproof.endSequent must beEqualTo( HOLSequent( pb :: Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( aeqb :: ipl :: Nil, pa :: Nil ) )
    }

    "correctly interpolate a proof containing EqualityLeft with a=b ∧ Top" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityLeftRule( proof, aeqb, Ant( 1 ), pb )

      val npart = Seq( Ant( 1 ) )
      val ppart = Seq( Ant( 0 ), Suc( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( And( aeqb, Top() ) )
      nproof.endSequent must beEqualTo( HOLSequent( aeqb :: Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: pb :: Nil, pa :: Nil ) )
    }

    "correctly interpolate a proof containing EqualityLeft with a=b ∧ Neg( P(a) )" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityLeftRule( proof, aeqb, Ant( 1 ), pb )

      val npart = Seq( Ant( 1 ), Suc( 0 ) )
      val ppart = Seq( Ant( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( And( aeqb, Neg( pa ) ) )
      nproof.endSequent must beEqualTo( HOLSequent( aeqb :: Nil, pa :: ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: pb :: Nil, Nil ) )
    }

    "correctly interpolate a proof containing EqualityLeft with a=b → Bottom" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityLeftRule( proof, aeqb, Ant( 1 ), pb )

      val npart = Seq( Ant( 0 ), Suc( 0 ) )
      val ppart = Seq( Ant( 1 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Imp( aeqb, Bottom() ) )
      nproof.endSequent must beEqualTo( HOLSequent( pb :: Nil, pa :: ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( aeqb :: ipl :: Nil, Nil ) )
    }

    "correctly interpolate a proof containing EqualityRight with Bottom" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityRightRule( proof, aeqb, Suc( 0 ), pb )

      val npart = proof1.endSequent.indices
      val ppart = Seq.empty[SequentIndex]

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.endSequent must beEqualTo( HOLSequent( aeqb :: pa :: Nil, ipl :: pb :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Nil ) )
    }

    "correctly interpolate a proof containing EqualityRight with Top" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityRightRule( proof, aeqb, Suc( 0 ), pb )

      val npart = Seq.empty[SequentIndex]
      val ppart = proof1.endSequent.indices

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Top() )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( aeqb :: ipl :: pa :: Nil, pb :: Nil ) )
    }

    "correctly interpolate a proof containing EqualityRight with a=b ∧ P(a)" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityRightRule( proof, aeqb, Suc( 0 ), pb )

      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( And( aeqb, pa ) )
      nproof.endSequent must beEqualTo( HOLSequent( aeqb :: pa :: Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, pb :: Nil ) )
    }

    "correctly interpolate a proof containing EqualityRight with a=b → Neg( P(a) )" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityRightRule( proof, aeqb, Suc( 0 ), pb )

      val npart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )
      val ppart = proof1.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Imp( aeqb, Neg( pa ) ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, pb :: ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( aeqb :: ipl :: pa :: Nil, Nil ) )
    }

    "correctly interpolate a proof containing EqualityRight with P(a)" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityRightRule( proof, aeqb, Suc( 0 ), pb )

      val npart = Seq( Ant( 1 ) )
      val ppart = Seq( Ant( 0 ), Suc( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( pa )
      nproof.endSequent must beEqualTo( HOLSequent( pa :: Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( aeqb :: ipl :: Nil, pb :: Nil ) )
    }

    "correctly interpolate a proof containing EqualityRight with a=b → Bottom" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityRightRule( proof, aeqb, Suc( 0 ), pb )

      val npart = Seq( Ant( 0 ) )
      val ppart = Seq( Ant( 1 ), Suc( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( And( aeqb, Top() ) )
      nproof.endSequent must beEqualTo( HOLSequent( aeqb :: Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: pa :: Nil, pb :: Nil ) )
    }

    "correctly interpolate a proof containing EqualityRight with Neg( P(a) )" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityRightRule( proof, aeqb, Suc( 0 ), pb )

      val npart = Seq( Ant( 0 ), Suc( 0 ) )
      val ppart = Seq( Ant( 1 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Neg( pa ) )
      nproof.endSequent must beEqualTo( HOLSequent( aeqb :: Nil, ipl :: pb :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: pa :: Nil, Nil ) )
    }

    "correctly interpolate a proof containing EqualityRight with a=b → Bottom" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityRightRule( proof, aeqb, Suc( 0 ), pb )

      val npart = Seq( Ant( 1 ), Suc( 0 ) )
      val ppart = Seq( Ant( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof1, npart, ppart )

      ipl must beEqualTo( Imp( aeqb, Bottom() ) )
      nproof.endSequent must beEqualTo( HOLSequent( pa :: Nil, pb :: ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( aeqb :: ipl :: Nil, Nil ) )
    }

    "correctly interpolate a trivial atomic cut with Bottom ∨ P" in {
      val p = FOLAtom( "p", Nil )

      val axp = LogicalAxiom( p )
      val proof = CutRule( axp, p, axp, p )

      val npart = Seq( Ant( 0 ) )
      val ppart = Seq( Suc( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( Or( Bottom(), p ) )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, p :: Nil ) )
    }

    "correctly interpolate a trivial atomic cut (different partition) with Neg( p ) ∨ Bottom" in {
      val p = FOLAtom( "p", Nil )

      val axp = LogicalAxiom( p )
      val proof = CutRule( axp, p, axp, p )

      val npart = Seq( Suc( 0 ) )
      val ppart = Seq( Ant( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( Or( Neg( p ), Bottom() ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, p :: ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: p :: Nil, Nil ) )
    }

    "correctly interpolate a trivial atomic cut (yet another partition) with Bottom ∨ Bottom" in {
      val p = FOLAtom( "p", Nil )

      val axp = LogicalAxiom( p )
      val proof = CutRule( axp, p, axp, p )

      val npart = proof.endSequent.indices
      val ppart = Seq[SequentIndex]()

      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( Or( Bottom(), Bottom() ) )
      nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Nil ) )
    }

    "correctly interpolate a trivial atomic cut (and another partition) with Top ∨ Top" in {
      val p = FOLAtom( "p", Nil )

      val axp = LogicalAxiom( p )
      val proof = CutRule( axp, p, axp, p )

      val npart = Seq[SequentIndex]()
      val ppart = proof.endSequent.indices

      val ( nproof, pproof, ipl ) = Interpolate( proof, npart, ppart )

      ipl must beEqualTo( And( Top(), Top() ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: p :: Nil, p :: Nil ) )
    }

    "correctly interpolate a small proof with a single atomic cut" in {
      val p = FOLAtom( "p", Nil )
      val q = FOLAtom( "q", Nil )
      val r = FOLAtom( "r", Nil )

      val axp = LogicalAxiom( p )
      val axq = LogicalAxiom( q )
      val axr = LogicalAxiom( r )
      val proof = NegLeftRule( axq, q )
      val proof1 = OrLeftRule( proof, q, axr, r )
      val proof2 = ImpRightRule( proof1, Neg( q ), r )
      val proof3 = ImpLeftRule( axp, p, proof2, Or( q, r ) )
      val proof4 = WeakeningRightRule( proof3, p )
      val proof5 = CutRule( proof4, axp, p )

      val npart = proof5.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof5.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )

      val ( nproof, pproof, ipl ) = Interpolate( proof5, npart, ppart )

      ipl must beEqualTo( Or( Or( Bottom(), Or( q, r ) ), p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Imp( p, Or( q, r ) ) :: p :: Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Imp( Neg( q ), r ) :: p :: Nil ) )
    }

    "correctly interpolate another small proof with a single atomic cut" in {
      val p = FOLAtom( "p", Nil )
      val q = FOLAtom( "q", Nil )
      val r = FOLAtom( "r", Nil )

      val axp = LogicalAxiom( p )
      val axq = LogicalAxiom( q )
      val axr = LogicalAxiom( r )
      val proof = NegLeftRule( axq, q )
      val proof1 = OrLeftRule( proof, q, axr, r )
      val proof2 = ImpRightRule( proof1, Neg( q ), r )
      val proof3 = ImpLeftRule( axp, p, proof2, Or( q, r ) )
      val proof4 = WeakeningRightRule( proof3, q )
      val proof5 = WeakeningLeftRule( axp, q )
      val proof6 = CutRule( proof4, proof5, q )

      val npart = proof6.endSequent.indices.filter( ind => ind.isInstanceOf[Ant] )
      val ppart = proof6.endSequent.indices.filter( ind => ind.isInstanceOf[Suc] )

      val ( nproof, pproof, ipl ) = Interpolate( proof6, npart, ppart )

      ipl must beEqualTo( Or( Or( Bottom(), Or( q, r ) ), p ) )
      nproof.endSequent must beEqualTo( HOLSequent( Imp( p, Or( q, r ) ) :: p :: p :: Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Imp( Neg( q ), r ) :: p :: Nil ) )
    }

    "correctly interpolate a proof with two atomic cuts" in {
      val p = FOLAtom( "p", Nil )

      val axp = LogicalAxiom( p )

      val negp = Neg( p )
      val nnegp = Neg( negp )

      val proof = NegRightRule( axp, p )
      val proof1 = NegLeftRule( proof, negp )
      val proof2 = WeakeningRightRule( proof1, p )
      val proof3 = ImpRightRule( proof2, nnegp, p )

      val proof4 = NegLeftRule( axp, p )
      val proof5 = WeakeningRightRule( proof4, p )
      val proof6 = OrLeftRule( axp, p, proof5, negp )
      val proof7 = ContractionRightRule( proof6, p )

      val proof8 = WeakeningLeftRule( axp, nnegp )
      val proof9 = ImpRightRule( proof8, nnegp, p )
      val proof10 = CutRule( proof7, proof9, p )

      val proof11 = CutRule( proof3, proof10, p )

      val proof12 = ContractionRightRule( proof11, Imp( nnegp, p ) )

      val npart = Seq( Ant( 0 ) )
      val ppart = Seq( Suc( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof12, npart, ppart )

      ipl must beEqualTo( Or( Top(), Or( Or( Bottom(), Bottom() ), p ) ) )
      nproof.endSequent must beEqualTo( HOLSequent( Or( p, Neg( p ) ) :: Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Imp( Neg( Neg( p ) ), p ) :: Nil ) )
    }

    "correctly interpolate a proof with two cuts and two equality right rules" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val axab = LogicalAxiom( aeqb )

      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityRightRule( proof, aeqb, pa, pb )

      val proof2 = CutRule( axab, proof1, aeqb )
      val proof3 = ImpRightRule( proof2, pa, pb )

      val proof4 = WeakeningLeftRule( axpb, aeqb )
      val proof5 = EqualityRightRule( proof4, aeqb, pb, pa )

      val proof6 = CutRule( axab, proof5, aeqb )
      val proof7 = ImpRightRule( proof6, pb, pa )

      val proof8 = AndRightRule( proof3, Imp( pa, pb ), proof7, Imp( pb, pa ) )
      val proof9 = ContractionLeftRule( proof8, aeqb )
      val proof10 = ImpRightRule( proof9, aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) )

      val npart = Seq( Suc( 0 ) )
      val ppart = Seq[SequentIndex]()

      val ( nproof, pproof, ipl ) = Interpolate( proof10, npart, ppart )

      val Il = Or( Bottom(), Bottom() )
      val Ir = Or( Bottom(), Bottom() )

      ipl must beEqualTo( Or( Il, Ir ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Imp( aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Nil ) )
    }

    "correctly interpolate a proof with two cuts and two equality right rules (different partition)" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val axab = LogicalAxiom( aeqb )

      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityRightRule( proof, aeqb, pa, pb )

      val proof2 = CutRule( axab, proof1, aeqb )
      val proof3 = ImpRightRule( proof2, pa, pb )

      val proof4 = WeakeningLeftRule( axpb, aeqb )
      val proof5 = EqualityRightRule( proof4, aeqb, pb, pa )

      val proof6 = CutRule( axab, proof5, aeqb )
      val proof7 = ImpRightRule( proof6, pb, pa )

      val proof8 = AndRightRule( proof3, Imp( pa, pb ), proof7, Imp( pb, pa ) )
      val proof9 = ContractionLeftRule( proof8, aeqb )
      val proof10 = ImpRightRule( proof9, aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) )

      val npart = Seq[SequentIndex]()
      val ppart = Seq( Suc( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof10, npart, ppart )

      val Il = And( Top(), Top() )
      val Ir = And( Top(), Top() )

      ipl must beEqualTo( And( Il, Ir ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Imp( aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) ) :: Nil ) )
    }

    "correctly interpolate a proof with two cuts and two equality left rules" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val axab = LogicalAxiom( aeqb )

      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityLeftRule( proof, aeqb, pa, pb )

      val proof2 = CutRule( axab, proof1, aeqb )
      val proof3 = ImpRightRule( proof2, pb, pa )

      val proof4 = WeakeningLeftRule( axpb, aeqb )
      val proof5 = EqualityLeftRule( proof4, aeqb, pb, pa )

      val proof6 = CutRule( axab, proof5, aeqb )
      val proof7 = ImpRightRule( proof6, pa, pb )

      val proof8 = AndRightRule( proof3, Imp( pb, pa ), proof7, Imp( pa, pb ) )
      val proof9 = ContractionLeftRule( proof8, aeqb )
      val proof10 = ImpRightRule( proof9, aeqb, And( Imp( pb, pa ), Imp( pa, pb ) ) )

      val npart = Seq( Suc( 0 ) )
      val ppart = Seq[SequentIndex]()

      val ( nproof, pproof, ipl ) = Interpolate( proof10, npart, ppart )

      val Il = Or( Bottom(), Bottom() )
      val Ir = Or( Bottom(), Bottom() )

      ipl must beEqualTo( Or( Il, Ir ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Imp( aeqb, And( Imp( pb, pa ), Imp( pa, pb ) ) ) :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Nil ) )
    }

    "correctly interpolate a proof with two cuts and two equality left rules (different partition)" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = LogicalAxiom( pa )
      val axpb = LogicalAxiom( pb )
      val axab = LogicalAxiom( aeqb )

      val proof = WeakeningLeftRule( axpa, aeqb )
      val proof1 = EqualityLeftRule( proof, aeqb, pa, pb )

      val proof2 = CutRule( axab, proof1, aeqb )
      val proof3 = ImpRightRule( proof2, pb, pa )

      val proof4 = WeakeningLeftRule( axpb, aeqb )
      val proof5 = EqualityLeftRule( proof4, aeqb, pb, pa )

      val proof6 = CutRule( axab, proof5, aeqb )
      val proof7 = ImpRightRule( proof6, pa, pb )

      val proof8 = AndRightRule( proof3, Imp( pb, pa ), proof7, Imp( pa, pb ) )
      val proof9 = ContractionLeftRule( proof8, aeqb )
      val proof10 = ImpRightRule( proof9, aeqb, And( Imp( pb, pa ), Imp( pa, pb ) ) )

      val npart = Seq[SequentIndex]()
      val ppart = Seq( Suc( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( proof10, npart, ppart )

      val Il = And( Top(), Top() )
      val Ir = And( Top(), Top() )

      ipl must beEqualTo( And( Il, Ir ) )
      nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Nil ) )
      pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Imp( aeqb, And( Imp( pb, pa ), Imp( pa, pb ) ) ) :: Nil ) )
    }

  }
}
