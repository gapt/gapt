package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.nd.NDProof
import at.logic.gapt.proofs.{ Ant, Context, SequentIndex, SequentMatchers, Suc }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class LKToNDTest extends Specification with SatMatchers with SequentMatchers {

  def checkEquality( nd: NDProof, lk: LKProof, focus: SequentIndex ) = {
    if ( lk.endSequent.succedent.isEmpty ) {
      ( lk.endSequent.size + 1 ) mustEqual nd.endSequent.size
      nd.endSequent( Suc( 0 ) ) mustEqual Bottom()
    } else {
      lk.endSequent.size mustEqual nd.endSequent.size
      lk.endSequent.succedent.contains( nd.endSequent( Suc( 0 ) ) ) mustEqual true
      lk.endSequent( focus ) mustEqual nd.endSequent( Suc( 0 ) )
    }
    lk.endSequent.antecedent.forall( nd.endSequent.antecedent.contains( _ ) ) mustEqual true
    lk.endSequent.succedent.filter( _ != nd.endSequent( Suc( 0 ) ) ).forall( x => nd.endSequent.antecedent.contains( Neg( x ) ) ) mustEqual true
  }

  "The LK to ND translation" should {

    "translate DeMorgan's law Or To And" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( OrRightRule( _, hof"A | B" ) ).
        u( NegLeftRule( _, hof"A | B" ) ).
        u( NegRightRule( _, hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( OrRightRule( _, hof"A | B" ) ).
        u( NegLeftRule( _, hof"A | B" ) ).
        u( NegRightRule( _, hof"B" ) ).
        b( AndRightRule( _, _, hof"-A & -B" ) ).
        u( ContractionLeftRule( _, hof"-(A | B)" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate DeMorgan's law And To Or" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        u( WeakeningLeftRule( _, hof"B" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( NegLeftRule( _, hof"B" ) ).
        u( WeakeningLeftRule( _, hof"A" ) ).
        b( OrLeftRule( _, _, hof"-A | -B" ) ).
        u( ContractionLeftRule( _, hof"A" ) ).
        u( ContractionLeftRule( _, hof"B" ) ).
        u( AndLeftRule( _, hof"A & B" ) ).
        u( NegRightRule( _, hof"A & B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate AndRight with focus 0" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        b( AndRightRule( _, Suc( 0 ), _, Suc( 0 ) ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate AndRight with focus 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        b( AndRightRule( _, Suc( 0 ), _, Suc( 0 ) ) ).
        qed

      val focus = Suc( 1 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrLeft 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        b( OrLeftRule( _, _, hof"A | B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrLeft 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"A" ) ).
        b( OrLeftRule( _, _, hof"A | A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrLeft 3" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        u( WeakeningLeftRule( _, hof"D" ) ).
        b( OrLeftRule( _, _, hof"A | D" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrLeft 4 with focus 3" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        u( WeakeningLeftRule( _, hof"D" ) ).
        b( OrLeftRule( _, _, hof"A | D" ) ).
        qed

      val focus = Suc( 3 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrLeft 5 with focus 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"A" ) ).
        u( NegRightRule( _, hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        b( OrLeftRule( _, _, hof"A | B" ) ).
        qed

      val focus = Suc( 2 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ImpRight 1 with focus 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( ImpRightRule( _, hof"A -> B" ) ).
        qed

      val focus = Suc( 1 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ImpRight 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( ImpRightRule( _, hof"A -> B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrRight case 1 with focus 0" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( OrRightRule( _, hof"A | B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrRight case 1 with focus 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( OrRightRule( _, hof"A | B" ) ).
        qed

      val focus = Suc( 1 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrRight case 2 with Weakening" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        u( OrRightRule( _, hof"A | B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrRight case 2 with Negation" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"B" ) ).
        u( NegRightRule( _, hof"B" ) ).
        u( OrRightRule( _, hof"A | -B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate NegLeft followed by NegRight" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        u( NegRightRule( _, hof"-A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrLeft followed by NegRight with focus 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        b( OrLeftRule( _, _, hof"A | B" ) ).
        u( NegRightRule( _, hof"A | B" ) ).
        qed

      val focus = Suc( 1 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrLeft followed by NegRight with focus 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        b( OrLeftRule( _, _, hof"A | B" ) ).
        u( NegRightRule( _, hof"A | B" ) ).
        qed

      val focus = Suc( 2 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate NegRight" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"B" ) ).
        u( NegRightRule( _, hof"B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningRight followed by ContractRight" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( ContractionRightRule( _, hof"A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate Cut 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"A" ) ).
        b( CutRule( _, Suc( 0 ), _, Ant( 0 ) ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate Cut 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"B" ) ).
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        b( CutRule( _, Suc( 0 ), _, Ant( 0 ) ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ImpLeft with focus 0" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningLeftRule( _, hof"D" ) ).
        b( ImpLeftRule( _, _, hof"A -> B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ImpLeft with focus 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( WeakeningLeftRule( _, hof"D" ) ).
        b( ImpLeftRule( _, _, hof"A -> B" ) ).
        qed

      val focus = Suc( 1 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate LEM" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegRightRule( _, hof"A" ) ).
        u( OrRightRule( _, hof"A | -A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningRight with focus 0" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningRight with focus 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        qed

      val focus = Suc( 1 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningRight with focus 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        qed

      val focus = Suc( 2 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate example 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        u( WeakeningRightRule( _, hof"D" ) ).
        u( OrRightRule( _, hof"A | B" ) ).
        u( NegLeftRule( _, hof"A | B" ) ).
        u( OrRightRule( _, hof"C | D" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ForAll left and right" in {
      implicit var ctx = Context()
      ctx += TBase( "i" )
      ctx += hoc"A: i > o"

      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A t" ) ).
        u( ForallLeftRule( _, hof"!x A x", fov"t" ) ).
        u( ForallRightRule( _, hof"!x A x", fov"t" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ExistsRight" in {
      implicit var ctx = Context()
      ctx += TBase( "i" )
      ctx += hoc"A: i > o"

      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A v" ) ).
        u( ExistsRightRule( _, hof"?x A x", fov"v" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate Exists right and left" in {
      implicit var ctx = Context()
      ctx += TBase( "i" )
      ctx += hoc"A: i > o"

      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A v" ) ).
        u( ExistsRightRule( _, hof"?x A x", fov"v" ) ).
        u( ExistsLeftRule( _, hof"?x A x", fov"v" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningLeft followed by ContractLeft" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"A" ) ).
        u( ContractionLeftRule( _, hof"A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningLeft with empty succedent" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        u( WeakeningLeftRule( _, hof"B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ContractionLeft with empty succedent" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        u( WeakeningLeftRule( _, hof"A" ) ).
        u( ContractionLeftRule( _, hof"A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate AndLeft with empty succedent" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        u( AndLeftRule( _, hof"A & -A" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrLeft with empty succedent" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( NegLeftRule( _, hof"B" ) ).
        b( OrLeftRule( _, _, hof"A | B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate AndLeft and OrLeft with focus on 'wrong' formula" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( WeakeningRightRule( _, hof"C" ) ).
        u( OrRightRule( _, hof"A | B" ) ).
        c( LogicalAxiom( hof"D" ) ).
        b( AndRightRule( _, _, hof"C & D" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ImpLeft with empty succedent" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        u( NegLeftRule( _, hof"B" ) ).
        b( ImpLeftRule( _, _, hof"A -> B" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate Cut with empty succedent" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        b( CutRule( _, Suc( 0 ), _, Ant( 1 ) ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ForallLeft with empty succedent" in {
      implicit var ctx = Context()
      ctx += TBase( "i" )
      ctx += hoc"A: i > o"

      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A t" ) ).
        u( NegLeftRule( _, hof"A t" ) ).
        u( ForallLeftRule( _, hof"!x A x", fov"t" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ExistsLeft with empty succedent" in {
      implicit var ctx = Context()
      ctx += TBase( "i" )
      ctx += hoc"A: i > o"

      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A v" ) ).
        u( ExistsRightRule( _, hof"?x A x", fov"v" ) ).
        u( NegLeftRule( _, hof"?x A x" ) ).
        u( ExistsLeftRule( _, hof"?x A x", fov"v" ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate EqualityLeft 1" in {
      val c = FOLConst( "c" )
      val d = FOLConst( "d" )
      val Pc = FOLAtom( "P", c )
      val Pd = FOLAtom( "P", d )

      val lk = ProofBuilder.
        c( LogicalAxiom( Pc ) ).
        u( WeakeningLeftRule( _, Pd ) ).
        u( WeakeningRightRule( _, Pd ) ).
        u( WeakeningLeftRule( _, hof"$c = $d" ) ).
        u( EqualityLeftRule( _, Eq( c, d ), Pc, Pd ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate EqualityRight 1" in {
      val c = FOLConst( "c" )
      val d = FOLConst( "d" )
      val Pc = FOLAtom( "P", c )
      val Pd = FOLAtom( "P", d )

      val lk = ProofBuilder.
        c( LogicalAxiom( Pc ) ).
        u( WeakeningLeftRule( _, Pd ) ).
        u( WeakeningRightRule( _, Pd ) ).
        u( WeakeningLeftRule( _, hof"$c = $d" ) ).
        u( EqualityRightRule( _, Eq( c, d ), Pc, Pd ) ).
        qed

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate InductionRule" in {
      val x = FOLVar( "x" )
      val y = FOLVar( "y" )
      val zero = FOLConst( "0" )
      val Sx = FOLFunction( "s", List( x ) )

      val P0y = FOLAtom( "P", List( zero, y ) )
      val Pxy = FOLAtom( "P", List( x, y ) )
      val PSxy = FOLAtom( "P", List( Sx, y ) )

      val ax1 = LogicalAxiom( P0y )

      val ax2 = ProofLink( foc"th", hos"$Pxy :- $PSxy" )

      val lk = InductionRule(
        Seq(
          InductionCase( ax1, FOLConst( "0" ), Seq(), Seq(), Suc( 0 ) ),
          InductionCase( ax2, FOLFunctionConst( "s", 1 ), Seq( Ant( 0 ) ), Seq( x ), Suc( 0 ) )
        ),
        Abs( x, Pxy ), x
      )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

  }
}

