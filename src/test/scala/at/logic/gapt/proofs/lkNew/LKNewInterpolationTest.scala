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
  }
}
