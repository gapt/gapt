package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
import org.specs2.execute.Success
import org.specs2.mutable._

class LKNewInterpolationTest extends Specification with SequentMatchers {

  "correctly interpolate a logical axiom with top" in {
    val ax = LogicalAxiom( hof"p" )
    ExtractInterpolant( ax, ax.conclusion.map( _ => true ) ) must_== Top()
  }

  "correctly interpolate a logical axiom with bottom" in {
    val ax = LogicalAxiom( hof"p" )
    ExtractInterpolant( ax, ax.conclusion.map( _ => false ) ) must_== Bottom()
  }

  "correctly interpolate a logical axiom with the atom of the axiom itself" in {
    val ax = LogicalAxiom( hof"p" )
    ExtractInterpolant( ax, ax.endSequent.indicesSequent.map( _.isSuc ) ) must_== hof"p"
  }

  "correctly interpolate a logical axiom with the negated atom of the axiom itself" in {
    val ax = LogicalAxiom( hof"p" )
    ExtractInterpolant( ax, ax.endSequent.indicesSequent.map( _.isAnt ) ) must_== hof"-p"
  }

  "correctly interpolate a TopAxiom with bottom" in {
    ExtractInterpolant( TopAxiom, Seq() :- Seq( false ) ) must_== Bottom()
  }

  "correctly interpolate a TopAxiom with top" in {
    ExtractInterpolant( TopAxiom, Seq() :- Seq( true ) ) must_== Top()
  }

  "correctly interpolate a BottomAxiom with bottom" in {
    ExtractInterpolant( BottomAxiom, Seq( false ) :- Seq() ) must_== Bottom()
  }

  "correctly interpolate a BottomAxiom with top" in {
    ExtractInterpolant( BottomAxiom, Seq( true ) :- Seq() ) must_== Top()
  }

  "correctly interpolate a ReflexivityAxiom with bottom" in {
    ExtractInterpolant( ReflexivityAxiom( le"c" ), Seq() :- Seq( false ) ) must_== Bottom()
  }

  "correctly interpolate a ReflexivityAxiom with top" in {
    ExtractInterpolant( ReflexivityAxiom( le"c" ), Seq() :- Seq( true ) ) must_== Top()
  }

  "correctly create a proof containing WeakeningLeft with Bottom" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof, proof.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( hof"q" :: hof"p" :: Nil, hof"p" :: Bottom() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
  }

  "correctly create a proof containing WeakeningLeft (different partition) with p" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof, proof.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( hof"p" )
    nproof.endSequent must beEqualTo( HOLSequent( hof"q" :: hof"p" :: Nil, hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Nil ) )
  }

  "correctly create a proof containing WeakeningLeft (with yet another partition) with Neg( p )" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof, proof.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Neg( hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"p" :: Neg( hof"p" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"q" :: Neg( hof"p" ) :: hof"p" :: Nil, Nil ) )
  }

  "correctly create a proof containing WeakeningLeft (and another partition) with Top" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof, proof.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"q" :: Top() :: hof"p" :: Nil, hof"p" :: Nil ) )
  }

  "correctly create a proof containing WeakeningRight with Bottom" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof, proof.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Bottom() :: hof"q" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
  }

  "correctly create a proof containing WeakeningRight (different partition) with p" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof, proof.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( hof"p" )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: hof"q" :: Nil ) )
  }

  "correctly create a proof containing WeakeningRight (with yet another partition) with Neg( p )" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof, proof.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Neg( hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"p" :: Neg( hof"p" ) :: hof"q" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Neg( hof"p" ) :: hof"p" :: Nil, Nil ) )
  }

  "correctly create a proof containing WeakeningRight (and another partition) with Top" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof, proof.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Top() :: hof"p" :: Nil, hof"p" :: hof"q" :: Nil ) )
  }

  "correctly create a proof containing ContractionLeft with Bottom" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = ContractionLeftRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Bottom() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
  }

  "correctly create a proof containing ContractionLeft (different partition) with p" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = ContractionLeftRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( hof"p" )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Nil ) )
  }

  "correctly create a proof containing ContractionLeft (with yet another partition) with Neg( p )" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = ContractionLeftRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Neg( hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"p" :: Neg( hof"p" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Neg( hof"p" ) :: Nil, Nil ) )
  }

  "correctly create a proof containing ContractionLeft (and another partition) with Top" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = ContractionLeftRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Top() :: Nil, hof"p" :: Nil ) )
  }

  "correctly create a proof containing ContractionRight with Bottom" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = ContractionRightRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, Bottom() :: hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
  }

  "correctly create a proof containing ContractionRight (different partition) with p" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = ContractionRightRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( hof"p" )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Nil ) )
  }

  "correctly create a proof containing ContractionRight (with yet another partition) with Neg( p )" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = ContractionRightRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Neg( hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Neg( hof"p" ) :: hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Neg( hof"p" ) :: hof"p" :: Nil, Nil ) )
  }

  "correctly create a proof containing ContractionRight (and another partition) with Top" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = ContractionRightRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Top() :: hof"p" :: Nil, hof"p" :: Nil ) )
  }

  "correctly create a proof containing NegationLeft with Bottom" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = NegLeftRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( Neg( hof"p" ) :: hof"p" :: Nil, Bottom() :: hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
  }

  "correctly create a proof containing NegationLeft (different partition) with Bottom" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = NegLeftRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( Neg( hof"p" ) :: hof"p" :: Nil, Bottom() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, hof"p" :: Nil ) )
  }

  "correctly create a proof containing NegationLeft (with yet another partition) with Top" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = NegLeftRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Neg( hof"p" ) :: Top() :: hof"p" :: Nil, Nil ) )
  }

  "correctly create a proof containing NegationLeft (and another partition) with Top" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = NegLeftRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Neg( hof"p" ) :: Top() :: hof"p" :: Nil, hof"p" :: Nil ) )
  }

  "correctly create a proof containing NegationRight with Bottom" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = NegRightRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Bottom() :: Neg( hof"p" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
  }

  "correctly create a proof containing NegationRight (different partition) with p" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = NegRightRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( hof"p" )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Neg( hof"p" ) :: Nil ) )
  }

  "correctly create a proof containing NegationRight (with yet another partition) with Neg( p )" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = NegRightRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Neg( hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"p" :: Neg( hof"p" ) :: Neg( hof"p" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Neg( hof"p" ) :: hof"p" :: Nil, Nil ) )
  }

  "correctly create a proof containing NegationRight (and another partition) with Top" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = NegRightRule( proof, hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Top() :: hof"p" :: Nil, hof"p" :: Neg( hof"p" ) :: Nil ) )
  }

  "correctly create a proof containing AndLeft with Bottom" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = WeakeningLeftRule( proof, hof"q" )
    val proof2 = AndLeftRule( proof1, hof"p", hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof2, proof2.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( And( hof"p", hof"q" ) :: Nil, hof"p" :: Bottom() :: hof"q" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
  }

  "correctly create a proof containing AndLeft (different partition) with p" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = WeakeningLeftRule( proof, hof"q" )
    val proof2 = AndLeftRule( proof1, hof"p", hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof2, proof2.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( hof"p" )
    nproof.endSequent must beEqualTo( HOLSequent( And( hof"p", hof"q" ) :: Nil, hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: hof"q" :: Nil ) )
  }

  "correctly create a proof containing AndLeft (yet another partition) with Neg( p )" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = WeakeningLeftRule( proof, hof"q" )
    val proof2 = AndLeftRule( proof1, hof"p", hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof2, proof2.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Neg( hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"p" :: Neg( hof"p" ) :: hof"q" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( hof"p", hof"q" ) :: Neg( hof"p" ) :: Nil, Nil ) )
  }

  "correctly create a proof containing AndLeft (and another partition) with Top" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = WeakeningLeftRule( proof, hof"q" )
    val proof2 = AndLeftRule( proof1, hof"p", hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof2, proof2.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( hof"p", hof"q" ) :: Top() :: Nil, hof"p" :: hof"q" :: Nil ) )
  }

  "correctly create a proof containing OrRight with Bottom" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = WeakeningLeftRule( proof, hof"q" )
    val proof2 = OrRightRule( proof1, hof"p", hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof2, proof2.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( hof"q" :: hof"p" :: Nil, Bottom() :: Or( hof"p", hof"q" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
  }

  "correctly create a proof containing OrRight (different partition) with p" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = WeakeningLeftRule( proof, hof"q" )
    val proof2 = OrRightRule( proof1, hof"p", hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof2, proof2.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( hof"p" )
    nproof.endSequent must beEqualTo( HOLSequent( hof"q" :: hof"p" :: Nil, hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, Or( hof"p", hof"q" ) :: Nil ) )
  }

  "correctly create a proof containing OrRight (yet another partition) with Neg( p )" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = WeakeningLeftRule( proof, hof"q" )
    val proof2 = OrRightRule( proof1, hof"p", hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof2, proof2.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Neg( hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Neg( hof"p" ) :: Or( hof"p", hof"q" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"q" :: Neg( hof"p" ) :: hof"p" :: Nil, Nil ) )
  }

  "correctly create a proof containing OrRight (and another partition) with Top" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = WeakeningLeftRule( proof, hof"q" )
    val proof2 = OrRightRule( proof1, hof"p", hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof2, proof2.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"q" :: Top() :: hof"p" :: Nil, Or( hof"p", hof"q" ) :: Nil ) )
  }

  "correctly create a proof containing ImpRight with Bottom" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = ImpRightRule( proof, hof"q", hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, Bottom() :: Imp( hof"q", hof"p" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
  }

  "correctly create a proof containing ImpRight (different partition) with p" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = ImpRightRule( proof, hof"q", hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( hof"p" )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"p" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, Imp( hof"q", hof"p" ) :: Nil ) )
  }

  "correctly create a proof containing ImpRight (yet another partition) Neg( p )" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = ImpRightRule( proof, hof"q", hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Neg( hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Neg( hof"p" ) :: Imp( hof"q", hof"p" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Neg( hof"p" ) :: hof"p" :: Nil, Nil ) )
  }

  "correctly create a proof containing ImpRight (and another partition) with Top" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = ImpRightRule( proof, hof"q", hof"p" )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Top() :: hof"p" :: Nil, Imp( hof"q", hof"p" ) :: Nil ) )
  }

  "correctly interpolate a single unary inference with not p with Neg( p )" in {
    val proof = WeakeningRightRule( LogicalAxiom( hof"p" ), hof"q" )
    val proof1 = OrRightRule( proof, hof"p", hof"q" )
    val npart = Seq( Suc( 0 ) )
    val ppart = Seq( Ant( 0 ) )
    val ( nproof, pproof, ipl ) = Interpolate( proof1, Seq( true ) :- Seq( false ) )

    ipl must beEqualTo( Neg( hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, Neg( hof"p" ) :: Or( hof"p", hof"q" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Neg( hof"p" ) :: hof"p" :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing OrLeftRule with (Bottom ∨ Bottom)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = OrLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Or( Bottom(), Bottom() ) )
    nproof.endSequent must beEqualTo( HOLSequent( Or( hof"p", hof"q" ) :: Nil, hof"p" :: hof"q" :: Or( Bottom(), Bottom() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), Bottom() ) :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing OrLeftRule (different partition) with (p ∨ q)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = OrLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( Or( hof"p", hof"q" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Or( hof"p", hof"q" ) :: Nil, Or( hof"p", hof"q" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( hof"p", hof"q" ) :: Nil, hof"p" :: hof"q" :: Nil ) )
  }

  "correctly interpolate a proof containing OrLeftRule (yet another partition) with (Neg( p ) ∧ Neg( q ))" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = OrLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( And( Neg( hof"p" ), Neg( hof"q" ) ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"p" :: hof"q" :: And( Neg( hof"p" ), Neg( hof"q" ) ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( Neg( hof"p" ), Neg( hof"q" ) ) :: Or( hof"p", hof"q" ) :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing OrLeftRule (and another partition) with (Top ∧ Top)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = OrLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( And( Top(), Top() ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, And( Top(), Top() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( Top(), Top() ) :: Or( hof"p", hof"q" ) :: Nil, hof"p" :: hof"q" :: Nil ) )
  }

  "correctly interpolate a proof containing OrLeftRule (and again another partition) with (Bottom ∨ q)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = OrLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( false ) :- Seq( false, true ) )

    ipl must beEqualTo( Or( Bottom(), hof"q" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Or( hof"p", hof"q" ) :: Nil, hof"p" :: Or( Bottom(), hof"q" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), hof"q" ) :: Nil, hof"q" :: Nil ) )
  }

  "correctly interpolate a proof containing OrLeftRule (and again and again...) with (Top ∧ Neg( q ))" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = OrLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( true ) :- Seq( true, false ) )

    ipl must beEqualTo( And( Top(), Neg( hof"q" ) ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"q" :: And( Top(), Neg( hof"q" ) ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( Top(), Neg( hof"q" ) ) :: Or( hof"p", hof"q" ) :: Nil, hof"p" :: Nil ) )
  }

  "correctly interpolate a proof containing OrLeftRule (and again and again...) with (Neg( p ) ∧ Top)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = OrLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( true ) :- Seq( false, true ) )

    ipl must beEqualTo( And( Neg( hof"p" ), Top() ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"p" :: And( Neg( hof"p" ), Top() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( Neg( hof"p" ), Top() ) :: Or( hof"p", hof"q" ) :: Nil, hof"q" :: Nil ) )
  }

  "correctly interpolate a proof containing OrLeftRule (and again and again...) with (p ∨ Bottom)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = OrLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( false ) :- Seq( true, false ) )

    ipl must beEqualTo( Or( hof"p", Bottom() ) )
    nproof.endSequent must beEqualTo( HOLSequent( Or( hof"p", hof"q" ) :: Nil, hof"q" :: Or( hof"p", Bottom() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( hof"p", Bottom() ) :: Nil, hof"p" :: Nil ) )
  }

  "correctly interpolate a proof containing AndRightRule with (Bottom ∨ Bottom)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = AndRightRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Or( Bottom(), Bottom() ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: hof"q" :: Nil, And( hof"p", hof"q" ) :: Or( Bottom(), Bottom() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), Bottom() ) :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing AndRightRule (different partition) with (p ∧ q)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = AndRightRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( And( hof"p", hof"q" ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: hof"q" :: Nil, And( hof"p", hof"q" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( hof"p", hof"q" ) :: Nil, And( hof"p", hof"q" ) :: Nil ) )
  }

  "correctly interpolate a proof containing AndRightRule (yet another partition) with (Neg( p ) ∧ Neg( q ))" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = AndRightRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Or( Neg( hof"p" ), Neg( hof"q" ) ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, And( hof"p", hof"q" ) :: Or( Neg( hof"p" ), Neg( hof"q" ) ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Neg( hof"p" ), Neg( hof"q" ) ) :: hof"p" :: hof"q" :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing AndRightRule (and another partition) with (Top ∧ Top)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = AndRightRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( And( Top(), Top() ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, And( Top(), Top() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( Top(), Top() ) :: hof"p" :: hof"q" :: Nil, And( hof"p", hof"q" ) :: Nil ) )
  }

  "correctly interpolate a proof containing AndRightRule (and again another partition) with (Neg( p ) ∨ Bottom)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = AndRightRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( true, false ) :- Seq( false ) )

    ipl must beEqualTo( Or( Neg( hof"p" ), Bottom() ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"q" :: Nil, And( hof"p", hof"q" ) :: Or( Neg( hof"p" ), Bottom() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Neg( hof"p" ), Bottom() ) :: hof"p" :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing AndRightRule (and again and again...) with (Top ∧ q)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = AndRightRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( true, false ) :- Seq( true ) )

    ipl must beEqualTo( And( Top(), hof"q" ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"q" :: Nil, And( Top(), hof"q" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( Top(), hof"q" ) :: hof"p" :: Nil, And( hof"p", hof"q" ) :: Nil ) )
  }

  "correctly interpolate a proof containing AndRightRule (and again and again...) with (p ∧ Top)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = AndRightRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( false, true ) :- Seq( true ) )

    ipl must beEqualTo( And( hof"p", Top() ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, And( hof"p", Top() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( hof"p", Top() ) :: hof"q" :: Nil, And( hof"p", hof"q" ) :: Nil ) )
  }

  "correctly interpolate a proof containing AndRightRule (and again and again...) with (Bottom ∨ Neg( q ))" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = AndRightRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( false, true ) :- Seq( false ) )

    ipl must beEqualTo( Or( Bottom(), Neg( hof"q" ) ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, And( hof"p", hof"q" ) :: Or( Bottom(), Neg( hof"q" ) ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), Neg( hof"q" ) ) :: hof"q" :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing ImpLeftRule with (Bottom ∨ Bottom)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = ImpLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Or( Bottom(), Bottom() ) )
    nproof.endSequent must beEqualTo( HOLSequent( Imp( hof"p", hof"q" ) :: hof"p" :: Nil, hof"q" :: Or( Bottom(), Bottom() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), Bottom() ) :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing ImpLeftRule (different partition) with (Bottom ∨ q)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = ImpLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( Or( Bottom(), hof"q" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Imp( hof"p", hof"q" ) :: hof"p" :: Nil, Or( Bottom(), hof"q" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), hof"q" ) :: Nil, hof"q" :: Nil ) )
  }

  "correctly interpolate a proof containing ImpLefttRule (yet another partition) with (Top ∧ Neg( q ))" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = ImpLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( And( Top(), Neg( hof"q" ) ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"q" :: And( Top(), Neg( hof"q" ) ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( Top(), Neg( hof"q" ) ) :: Imp( hof"p", hof"q" ) :: hof"p" :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing ImpLeftRule (and another partition) with (Top ∧ Top)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = ImpLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, proof4.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( And( Top(), Top() ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, And( Top(), Top() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( Top(), Top() ) :: Imp( hof"p", hof"q" ) :: hof"p" :: Nil, hof"q" :: Nil ) )
  }

  "correctly interpolate a proof containing ImpLeftRule (and again another partition) with (p ∧ Neg( q ))" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = ImpLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( true, false ) :- Seq( false ) )

    ipl must beEqualTo( And( hof"p", Neg( hof"q" ) ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, hof"q" :: And( hof"p", Neg( hof"q" ) ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( hof"p", Neg( hof"q" ) ) :: Imp( hof"p", hof"q" ) :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing ImpLeftRule (and again and again...) with (p ∧ Top)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = ImpLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( true, false ) :- Seq( true ) )

    ipl must beEqualTo( And( hof"p", Top() ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, And( hof"p", Top() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( And( hof"p", Top() ) :: Imp( hof"p", hof"q" ) :: Nil, hof"q" :: Nil ) )
  }

  "correctly interpolate a proof containing ImpLeftRule (and again and again...) with (Neg( p ) ∨ q)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = ImpLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( false, true ) :- Seq( true ) )

    ipl must beEqualTo( Or( Neg( hof"p" ), hof"q" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Imp( hof"p", hof"q" ) :: Nil, Or( Neg( hof"p" ), hof"q" ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Neg( hof"p" ), hof"q" ) :: hof"p" :: Nil, hof"q" :: Nil ) )
  }

  "correctly interpolate a proof containing ImpLeftRule (and again and again...) with (Neg( p ) ∨ Bottom)" in {
    val proof = WeakeningLeftRule( LogicalAxiom( hof"p" ), hof"p" )
    val proof1 = WeakeningRightRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = ContractionRightRule( proof1, hof"q" )
    val proof3 = ContractionLeftRule( proof, hof"p" )
    val proof4 = ImpLeftRule( proof3, hof"p", LogicalAxiom( hof"q" ), hof"q" )
    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( false, true ) :- Seq( false ) )

    ipl must beEqualTo( Or( Neg( hof"p" ), Bottom() ) )
    nproof.endSequent must beEqualTo( HOLSequent( Imp( hof"p", hof"q" ) :: Nil, hof"q" :: Or( Neg( hof"p" ), Bottom() ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Neg( hof"p" ), Bottom() ) :: hof"p" :: Nil, Nil ) )
  }

  "correctly interpolate a small proof with 4 inference rules" in {
    val axr = LogicalAxiom( hof"r" )
    val proof1 = NegLeftRule( LogicalAxiom( hof"q" ), hof"q" )
    val proof2 = OrLeftRule( proof1, hof"q", axr, hof"r" )
    val proof3 = ImpRightRule( proof2, Neg( hof"q" ), hof"r" )
    val proof4 = ImpLeftRule( LogicalAxiom( hof"p" ), hof"p", proof3, Or( hof"q", hof"r" ) )

    val ( nproof, pproof, ipl ) = Interpolate( proof4, Seq( false, false ) :- Seq( true ) )

    ipl must beEqualTo( Or( Bottom(), Or( hof"q", hof"r" ) ) )
    nproof.endSequent must beEqualTo( HOLSequent( Imp( hof"p", Or( hof"q", hof"r" ) ) :: hof"p" :: Nil, Or( Bottom(), Or( hof"q", hof"r" ) ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( Or( Bottom(), Or( hof"q", hof"r" ) ) :: Nil, Imp( Neg( hof"q" ), hof"r" ) :: Nil ) )
  }

  "correctly interpolate a proof containing EqualityLeft with Bottom" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityLeftRule( proof, hof"a=b", Ant( 1 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( hof"P b" :: hof"a=b" :: Nil, hof"P a" :: ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing EqualityLeft with Top" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityLeftRule( proof, hof"a=b", Ant( 1 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"P b" :: hof"a=b" :: ipl :: Nil, hof"P a" :: Nil ) )
  }

  "correctly interpolate a proof containing EqualityLeft with P(a)" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityLeftRule( proof, hof"a=b", Ant( 1 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( hof"P a" )
    nproof.endSequent must beEqualTo( HOLSequent( hof"P b" :: hof"a=b" :: Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, hof"P a" :: Nil ) )
  }

  "correctly interpolate a proof containing EqualityLeft with Neg( P(a) )" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityLeftRule( proof, hof"a=b", Ant( 1 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Neg( hof"P a" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"P a" :: ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"P b" :: hof"a=b" :: ipl :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing EqualityLeft with a=b → P(a)" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityLeftRule( proof, hof"a=b", Ant( 1 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, Seq( false, true ) :- Seq( true ) )

    ipl must beEqualTo( Imp( hof"a=b", hof"P a" ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"P b" :: Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: ipl :: Nil, hof"P a" :: Nil ) )
  }

  "correctly interpolate a proof containing EqualityLeft with a=b ∧ Top" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityLeftRule( proof, hof"a=b", Ant( 1 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, Seq( true, false ) :- Seq( true ) )

    ipl must beEqualTo( And( hof"a=b", Top() ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: hof"P b" :: Nil, hof"P a" :: Nil ) )
  }

  "correctly interpolate a proof containing EqualityLeft with a=b ∧ Neg( P(a) )" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityLeftRule( proof, hof"a=b", Ant( 1 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, Seq( true, false ) :- Seq( false ) )

    ipl must beEqualTo( And( hof"a=b", Neg( hof"P a" ) ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: Nil, hof"P a" :: ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: hof"P b" :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing EqualityLeft with a=b → Bottom" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityLeftRule( proof, hof"a=b", Ant( 1 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, Seq( false, true ) :- Seq( false ) )

    ipl must beEqualTo( Imp( hof"a=b", Bottom() ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"P b" :: Nil, hof"P a" :: ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: ipl :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing EqualityRight with Bottom" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityRightRule( proof, hof"a=b", Suc( 0 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _ => false ) )

    ipl must beEqualTo( Bottom() )
    nproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: hof"P a" :: Nil, ipl :: hof"P b" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing EqualityRight with Top" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityRightRule( proof, hof"a=b", Suc( 0 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.conclusion.map( _ => true ) )

    ipl must beEqualTo( Top() )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: ipl :: hof"P a" :: Nil, hof"P b" :: Nil ) )
  }

  "correctly interpolate a proof containing EqualityRight with a=b ∧ P(a)" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityRightRule( proof, hof"a=b", Suc( 0 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( And( hof"a=b", hof"P a" ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: hof"P a" :: Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, hof"P b" :: Nil ) )
  }

  "correctly interpolate a proof containing EqualityRight with a=b → Neg( P(a) )" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityRightRule( proof, hof"a=b", Suc( 0 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, proof1.conclusion.indicesSequent.map( _.isAnt ) )

    ipl must beEqualTo( Imp( hof"a=b", Neg( hof"P a" ) ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"P b" :: ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: ipl :: hof"P a" :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing EqualityRight with P(a)" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityRightRule( proof, hof"a=b", Suc( 0 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, Seq( true, false ) :- Seq( true ) )

    ipl must beEqualTo( hof"P a" )
    nproof.endSequent must beEqualTo( HOLSequent( hof"P a" :: Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: ipl :: Nil, hof"P b" :: Nil ) )
  }

  "correctly interpolate a proof containing EqualityRight with a=b → Bottom" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityRightRule( proof, hof"a=b", Suc( 0 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, Seq( false, true ) :- Seq( true ) )

    ipl must beEqualTo( And( hof"a=b", Top() ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: hof"P a" :: Nil, hof"P b" :: Nil ) )
  }

  "correctly interpolate a proof containing EqualityRight with Neg( P(a) )" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityRightRule( proof, hof"a=b", Suc( 0 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, Seq( false, true ) :- Seq( false ) )

    ipl must beEqualTo( Neg( hof"P a" ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: Nil, ipl :: hof"P b" :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: hof"P a" :: Nil, Nil ) )
  }

  "correctly interpolate a proof containing EqualityRight with a=b → Bottom" in {
    val axpb = LogicalAxiom( hof"P b" )
    val proof = WeakeningLeftRule( LogicalAxiom( hof"P a" ), hof"a=b" )
    val proof1 = EqualityRightRule( proof, hof"a=b", Suc( 0 ), hof"P b" )

    val ( nproof, pproof, ipl ) = Interpolate( proof1, Seq( true, false ) :- Seq( false ) )

    ipl must beEqualTo( Imp( hof"a=b", Bottom() ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"P a" :: Nil, hof"P b" :: ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( hof"a=b" :: ipl :: Nil, Nil ) )
  }

  "correctly interpolate a trivial atomic cut with Bottom ∨ P" in {
    val axp = LogicalAxiom( hof"p" )
    val proof = CutRule( axp, hof"p", axp, hof"p" )

    val ( nproof, pproof, ipl ) = Interpolate( proof, Seq( false ) :- Seq( true ) )

    ipl must beEqualTo( Or( Bottom(), hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( hof"p" :: Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, hof"p" :: Nil ) )
  }

  "correctly interpolate a trivial atomic cut (different partition) with Neg( p ) ∨ Bottom" in {
    val axp = LogicalAxiom( hof"p" )
    val proof = CutRule( axp, hof"p", axp, hof"p" )

    val ( nproof, pproof, ipl ) = Interpolate( proof, Seq( true ) :- Seq( false ) )

    ipl must beEqualTo( Or( Neg( hof"p" ), Bottom() ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, hof"p" :: ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: hof"p" :: Nil, Nil ) )
  }

  "correctly interpolate a trivial atomic cut (yet another partition) with Bottom ∨ Bottom" in {
    val p = hof"p"

    val axp = LogicalAxiom( p )
    val proof = CutRule( axp, p, axp, p )

    val ( nproof, pproof, ipl ) = Interpolate( proof, Seq( false ) :- Seq( false ) )

    ipl must beEqualTo( Or( Bottom(), Bottom() ) )
    nproof.endSequent must beEqualTo( HOLSequent( p :: Nil, p :: ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Nil ) )
  }

  "correctly interpolate a trivial atomic cut (and another partition) with Top ∨ Top" in {
    val axp = LogicalAxiom( hof"p" )
    val proof = CutRule( axp, axp, hof"p" )

    val ( nproof, pproof, ipl ) = Interpolate( proof, Seq( true ) :- Seq( true ) )

    ipl must beEqualTo( And( Top(), Top() ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: hof"p" :: Nil, hof"p" :: Nil ) )
  }

  "correctly interpolate a small proof with a single atomic cut" in {
    val axp = LogicalAxiom( hof"p" )
    val axq = LogicalAxiom( hof"q" )
    val axr = LogicalAxiom( hof"r" )
    val proof = NegLeftRule( axq, hof"q" )
    val proof1 = OrLeftRule( proof, hof"q", axr, hof"r" )
    val proof2 = ImpRightRule( proof1, Neg( hof"q" ), hof"r" )
    val proof3 = ImpLeftRule( axp, hof"p", proof2, Or( hof"q", hof"r" ) )
    val proof4 = WeakeningRightRule( proof3, hof"p" )
    val proof5 = CutRule( proof4, axp, hof"p" )

    val ( nproof, pproof, ipl ) = Interpolate( proof5, proof5.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( Or( Or( Bottom(), Or( hof"q", hof"r" ) ), hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Imp( hof"p", Or( hof"q", hof"r" ) ) :: hof"p" :: Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Imp( Neg( hof"q" ), hof"r" ) :: hof"p" :: Nil ) )
  }

  "correctly interpolate another small proof with a single atomic cut" in {
    val axp = LogicalAxiom( hof"p" )
    val axq = LogicalAxiom( hof"q" )
    val axr = LogicalAxiom( hof"r" )
    val proof = NegLeftRule( axq, hof"q" )
    val proof1 = OrLeftRule( proof, hof"q", axr, hof"r" )
    val proof2 = ImpRightRule( proof1, Neg( hof"q" ), hof"r" )
    val proof3 = ImpLeftRule( axp, hof"p", proof2, Or( hof"q", hof"r" ) )
    val proof4 = WeakeningRightRule( proof3, hof"q" )
    val proof5 = WeakeningLeftRule( axp, hof"q" )
    val proof6 = CutRule( proof4, proof5, hof"q" )

    val ( nproof, pproof, ipl ) = Interpolate( proof6, proof6.endSequent.indicesSequent.map( _.isSuc ) )

    ipl must beEqualTo( Or( Or( Bottom(), Or( hof"q", hof"r" ) ), hof"p" ) )
    nproof.endSequent must beEqualTo( HOLSequent( Imp( hof"p", Or( hof"q", hof"r" ) ) :: hof"p" :: hof"p" :: Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Imp( Neg( hof"q" ), hof"r" ) :: hof"p" :: Nil ) )
  }

  "correctly interpolate a proof with two atomic cuts" in {
    val axp = LogicalAxiom( hof"p" )

    val proof = NegRightRule( axp, hof"p" )
    val proof1 = NegLeftRule( proof, hof"-p" )
    val proof2 = WeakeningRightRule( proof1, hof"p" )
    val proof3 = ImpRightRule( proof2, hof"--p", hof"p" )

    val proof4 = NegLeftRule( axp, hof"p" )
    val proof5 = WeakeningRightRule( proof4, hof"p" )
    val proof6 = OrLeftRule( axp, hof"p", proof5, hof"-p" )
    val proof7 = ContractionRightRule( proof6, hof"p" )

    val proof8 = WeakeningLeftRule( axp, hof"--p" )
    val proof9 = ImpRightRule( proof8, hof"--p", hof"p" )
    val proof10 = CutRule( proof7, proof9, hof"p" )

    val proof11 = CutRule( proof3, proof10, hof"p" )

    val proof12 = ContractionRightRule( proof11, Imp( hof"--p", hof"p" ) )

    val ( nproof, pproof, ipl ) = Interpolate( proof12, Seq( false ) :- Seq( true ) )

    ipl must beEqualTo( Or( Top(), Or( Or( Bottom(), Bottom() ), hof"p" ) ) )
    nproof.endSequent must beEqualTo( HOLSequent( Or( hof"p", Neg( hof"p" ) ) :: Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Imp( Neg( Neg( hof"p" ) ), hof"p" ) :: Nil ) )
  }

  "correctly interpolate a proof with two cuts and two equality right rules" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val axab = LogicalAxiom( hof"a=b" )

    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityRightRule( proof, hof"a=b", hof"P a", hof"P b" )

    val proof2 = CutRule( axab, proof1, hof"a=b" )
    val proof3 = ImpRightRule( proof2, hof"P a", hof"P b" )

    val proof4 = WeakeningLeftRule( axpb, hof"a=b" )
    val proof5 = EqualityRightRule( proof4, hof"a=b", hof"P b", hof"P a" )

    val proof6 = CutRule( axab, proof5, hof"a=b" )
    val proof7 = ImpRightRule( proof6, hof"P b", hof"P a" )

    val proof8 = AndRightRule( proof3, Imp( hof"P a", hof"P b" ), proof7, Imp( hof"P b", hof"P a" ) )
    val proof9 = ContractionLeftRule( proof8, hof"a=b" )
    val proof10 = ImpRightRule( proof9, hof"a=b", And( Imp( hof"P a", hof"P b" ), Imp( hof"P b", hof"P a" ) ) )

    val ( nproof, pproof, ipl ) = Interpolate( proof10, Seq() :- Seq( false ) )

    val Il = Or( Bottom(), Bottom() )
    val Ir = Or( Bottom(), Bottom() )

    ipl must beEqualTo( Or( Il, Ir ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Imp( hof"a=b", And( Imp( hof"P a", hof"P b" ), Imp( hof"P b", hof"P a" ) ) ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Nil ) )
  }

  "correctly interpolate a proof with two cuts and two equality right rules (different partition)" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val axab = LogicalAxiom( hof"a=b" )

    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityRightRule( proof, hof"a=b", hof"P a", hof"P b" )

    val proof2 = CutRule( axab, proof1, hof"a=b" )
    val proof3 = ImpRightRule( proof2, hof"P a", hof"P b" )

    val proof4 = WeakeningLeftRule( axpb, hof"a=b" )
    val proof5 = EqualityRightRule( proof4, hof"a=b", hof"P b", hof"P a" )

    val proof6 = CutRule( axab, proof5, hof"a=b" )
    val proof7 = ImpRightRule( proof6, hof"P b", hof"P a" )

    val proof8 = AndRightRule( proof3, Imp( hof"P a", hof"P b" ), proof7, Imp( hof"P b", hof"P a" ) )
    val proof9 = ContractionLeftRule( proof8, hof"a=b" )
    val proof10 = ImpRightRule( proof9, hof"a=b", And( Imp( hof"P a", hof"P b" ), Imp( hof"P b", hof"P a" ) ) )

    val npart = Seq[SequentIndex]()
    val ppart = Seq( Suc( 0 ) )

    val ( nproof, pproof, ipl ) = Interpolate( proof10, Seq() :- Seq( true ) )

    val Il = And( Top(), Top() )
    val Ir = And( Top(), Top() )

    ipl must beEqualTo( And( Il, Ir ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Imp( hof"a=b", And( Imp( hof"P a", hof"P b" ), Imp( hof"P b", hof"P a" ) ) ) :: Nil ) )
  }

  "correctly interpolate a proof with two cuts and two equality left rules" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val axab = LogicalAxiom( hof"a=b" )

    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityLeftRule( proof, hof"a=b", hof"P a", hof"P b" )

    val proof2 = CutRule( axab, proof1, hof"a=b" )
    val proof3 = ImpRightRule( proof2, hof"P b", hof"P a" )

    val proof4 = WeakeningLeftRule( axpb, hof"a=b" )
    val proof5 = EqualityLeftRule( proof4, hof"a=b", hof"P b", hof"P a" )

    val proof6 = CutRule( axab, proof5, hof"a=b" )
    val proof7 = ImpRightRule( proof6, hof"P a", hof"P b" )

    val proof8 = AndRightRule( proof3, Imp( hof"P b", hof"P a" ), proof7, Imp( hof"P a", hof"P b" ) )
    val proof9 = ContractionLeftRule( proof8, hof"a=b" )
    val proof10 = ImpRightRule( proof9, hof"a=b", And( Imp( hof"P b", hof"P a" ), Imp( hof"P a", hof"P b" ) ) )

    val npart = Seq( Suc( 0 ) )
    val ppart = Seq[SequentIndex]()

    val ( nproof, pproof, ipl ) = Interpolate( proof10, Seq() :- Seq( false ) )

    val Il = Or( Bottom(), Bottom() )
    val Ir = Or( Bottom(), Bottom() )

    ipl must beEqualTo( Or( Il, Ir ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Imp( hof"a=b", And( Imp( hof"P b", hof"P a" ), Imp( hof"P a", hof"P b" ) ) ) :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Nil ) )
  }

  "correctly interpolate a proof with two cuts and two equality left rules (different partition)" in {
    val axpa = LogicalAxiom( hof"P a" )
    val axpb = LogicalAxiom( hof"P b" )
    val axab = LogicalAxiom( hof"a=b" )

    val proof = WeakeningLeftRule( axpa, hof"a=b" )
    val proof1 = EqualityLeftRule( proof, hof"a=b", hof"P a", hof"P b" )

    val proof2 = CutRule( axab, proof1, hof"a=b" )
    val proof3 = ImpRightRule( proof2, hof"P b", hof"P a" )

    val proof4 = WeakeningLeftRule( axpb, hof"a=b" )
    val proof5 = EqualityLeftRule( proof4, hof"a=b", hof"P b", hof"P a" )

    val proof6 = CutRule( axab, proof5, hof"a=b" )
    val proof7 = ImpRightRule( proof6, hof"P a", hof"P b" )

    val proof8 = AndRightRule( proof3, Imp( hof"P b", hof"P a" ), proof7, Imp( hof"P a", hof"P b" ) )
    val proof9 = ContractionLeftRule( proof8, hof"a=b" )
    val proof10 = ImpRightRule( proof9, hof"a=b", And( Imp( hof"P b", hof"P a" ), Imp( hof"P a", hof"P b" ) ) )

    val ( nproof, pproof, ipl ) = Interpolate( proof10, Seq() :- Seq( true ) )

    val Il = And( Top(), Top() )
    val Ir = And( Top(), Top() )

    ipl must beEqualTo( And( Il, Ir ) )
    nproof.endSequent must beEqualTo( HOLSequent( Nil, ipl :: Nil ) )
    pproof.endSequent must beEqualTo( HOLSequent( ipl :: Nil, Imp( hof"a=b", And( Imp( hof"P b", hof"P a" ), Imp( hof"P a", hof"P b" ) ) ) :: Nil ) )
  }

  "correctly interpolate a proof with weak quantifiers" in {
    val proof = ( ProofBuilder
      c LogicalAxiom( hof"p c" )
      u ( ForallLeftRule( _, hof"!x p(x)", le"c" ) )
      u ( ExistsRightRule( _, hof"?x p(x)", le"c" ) ) qed )

    "forall in negative part" in {
      val ( negProof, posProof, interpolant ) = Interpolate( proof, Seq( false ) :- Seq( true ) )
      interpolant must_== hof"p c"
      negProof.endSequent must beMultiSetEqual( hos"!x p(x) :- $interpolant" )
      posProof.endSequent must beMultiSetEqual( hos"$interpolant :- ?x p(x)" )
    }
    "exists in negative part" in {
      val ( negProof, posProof, interpolant ) = Interpolate( proof, Seq( true ) :- Seq( false ) )
      interpolant must_== hof"-p c"
      negProof.endSequent must beMultiSetEqual( hos":- ?x p(x), $interpolant" )
      posProof.endSequent must beMultiSetEqual( hos"$interpolant, !x p(x) :-" )
    }
  }

}
