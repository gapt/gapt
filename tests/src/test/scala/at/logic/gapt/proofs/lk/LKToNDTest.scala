package at.logic.gapt.proofs.lk

import at.logic.gapt.examples
import at.logic.gapt.expr._
import at.logic.gapt.formats.babel.{ Notation, Precedence }
import at.logic.gapt.proofs.nd.{ ExcludedMiddleRule, NDProof }
import at.logic.gapt.proofs.{ Ant, Context, SequentIndex, SequentMatchers, Suc }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class LKToNDTest extends Specification with SatMatchers with SequentMatchers {

  def checkEquality( nd: NDProof, lk: LKProof, focus: Option[SequentIndex] ) = {
    if ( lk.endSequent.succedent.isEmpty ) {
      ( lk.endSequent.size + 1 ) mustEqual nd.endSequent.size
      nd.endSequent( Suc( 0 ) ) mustEqual Bottom()
    } else {
      lk.endSequent.size mustEqual nd.endSequent.size
      lk.endSequent.succedent.contains( nd.endSequent( Suc( 0 ) ) ) mustEqual true
      lk.endSequent( focus.get ) mustEqual nd.endSequent( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 1 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrLeft 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"B" ) ).
        b( OrLeftRule( _, _, hof"A | B" ) ).
        qed

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate OrLeft 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"A" ) ).
        b( OrLeftRule( _, _, hof"A | A" ) ).
        qed

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 3 ) )
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

      val focus = Some( Suc( 2 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ImpRight 1 with focus 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( ImpRightRule( _, hof"A -> B" ) ).
        qed

      val focus = Some( Suc( 1 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ImpRight 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( ImpRightRule( _, hof"A -> B" ) ).
        qed

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 1 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate NegLeft followed by NegRight" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        u( NegRightRule( _, hof"-A" ) ).
        qed

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 1 ) )
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

      val focus = Some( Suc( 2 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate NegRight" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"B" ) ).
        u( NegRightRule( _, hof"B" ) ).
        qed

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningRight followed by ContractRight" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( ContractionRightRule( _, hof"A" ) ).
        qed

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate Cut 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        c( LogicalAxiom( hof"A" ) ).
        b( CutRule( _, Suc( 0 ), _, Ant( 0 ) ) ).
        qed

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 1 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate LEM" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegRightRule( _, hof"A" ) ).
        u( OrRightRule( _, hof"A | -A" ) ).
        qed

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningRight with focus 0" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        qed

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningRight with focus 1" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        qed

      val focus = Some( Suc( 1 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningRight with focus 2" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        qed

      val focus = Some( Suc( 2 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
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

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningLeft followed by ContractLeft" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningLeftRule( _, hof"A" ) ).
        u( ContractionLeftRule( _, hof"A" ) ).
        qed

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate WeakeningLeft with empty succedent" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        u( WeakeningLeftRule( _, hof"B" ) ).
        qed

      val focus = None
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

      val focus = None
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate AndLeft with empty succedent" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( NegLeftRule( _, hof"A" ) ).
        u( AndLeftRule( _, hof"A & -A" ) ).
        qed

      val focus = None
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

      val focus = None
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

      val focus = Some( Suc( 0 ) )
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

      val focus = None
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

      val focus = None
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

      val focus = None
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

      val focus = None
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate EqualityLeft" in {
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

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate EqualityLeft, empty succedent" in {
      val c = FOLConst( "c" )
      val d = FOLConst( "d" )
      val Pc = FOLAtom( "P", c )
      val Pd = FOLAtom( "P", d )

      val lk = ProofBuilder.
        c( LogicalAxiom( Pc ) ).
        u( NegLeftRule( _, Suc( 0 ) ) ).
        u( WeakeningLeftRule( _, Pd ) ).
        u( WeakeningLeftRule( _, hof"$c = $d" ) ).
        u( EqualityLeftRule( _, Eq( c, d ), Pc, Pd ) ).
        qed

      val focus = None
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate EqualityLeft, multiple replacements" in {
      val c = FOLConst( "c" )
      val d = FOLConst( "d" )
      val Pc = FOLAtom( "P", c )
      val Pd = FOLAtom( "P", d )
      val Pccc = FOLAtom( "P", c, c, c )
      val Pccd = FOLAtom( "P", c, c, d )

      val lk = ProofBuilder.
        c( LogicalAxiom( Pc ) ).
        u( WeakeningLeftRule( _, Pccc ) ).
        u( WeakeningLeftRule( _, Pd ) ).
        u( WeakeningRightRule( _, Pd ) ).
        u( WeakeningLeftRule( _, hof"$c = $d" ) ).
        u( EqualityLeftRule( _, Eq( c, d ), Pccc, Pccd ) ).
        qed

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate EqualityRight" in {
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

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate EqualityRight multiple replacements" in {
      val c = FOLConst( "c" )
      val d = FOLConst( "d" )
      val Pc = FOLAtom( "P", c )
      val Pd = FOLAtom( "P", d )
      val Pccc = FOLAtom( "P", c, c, c )
      val Pccd = FOLAtom( "P", c, c, d )

      val lk = ProofBuilder.
        c( LogicalAxiom( Pccc ) ).
        u( WeakeningLeftRule( _, Pd ) ).
        u( WeakeningRightRule( _, Pd ) ).
        u( WeakeningLeftRule( _, hof"$c = $d" ) ).
        u( EqualityRightRule( _, Eq( c, d ), Pccc, Pccd ) ).
        qed

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate InductionRule" in {
      val x = FOLVar( "x" )
      val zero = FOLConst( "0" )
      val Sx = FOLFunction( "s", List( x ) )

      val P0 = FOLAtom( "P", List( zero ) )
      val Px = FOLAtom( "P", List( x ) )
      val PSx = FOLAtom( "P", List( Sx ) )

      val ax1 = LogicalAxiom( P0 )

      implicit var ctx = Context.default
      ctx += Context.InductiveType( "i", hoc"0: i", hoc"s: i>i" )
      ctx += hoc"'th': i>i"
      ctx += hoc"'P': i>o"
      ctx += ( "th", hos"$Px :- $PSx" )

      val ax2 = ProofLink( le"th x", hos"$Px :- $PSx" )

      val lk = InductionRule(
        Seq(
          InductionCase( ax1, hoc"0: i", Seq(), Seq(), Suc( 0 ) ),
          InductionCase( ax2, hoc"s: i>i", Seq( Ant( 0 ) ), Seq( x ), Suc( 0 ) ) ),
        Abs( x, Px ), x )
      ctx.check( lk )

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ProofLink" in {
      implicit var ctx = Context.default
      ctx += Context.Sort( "i" )
      ctx += hoc"'<': i>i>o"
      ctx += hoc"'+': i>i>i"
      ctx += hoc"'1': i"
      ctx += hoc"'3': i"
      ctx += hoc"'ax': i>i>i"
      ctx += Notation.Infix( "<", Precedence.infixRel )
      ctx += Notation.Infix( "+", Precedence.plusMinus )
      ctx += ( "ax", hos"x + 1 < y :- x < y" )
      val lk = ProofLink( le"ax 1 3", hos"1 + 1 < 3 :- 1 < 3" )
      ctx.check( lk )

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ProofLink multiple antecedents" in {
      implicit var ctx = Context.default
      ctx += Context.Sort( "i" )
      ctx += hoc"'<': i>i>o"
      ctx += hoc"'1': i"
      ctx += hoc"'2': i"
      ctx += hoc"'3': i"
      ctx += hoc"'ax': i>i>i>i"
      ctx += Notation.Infix( "<", Precedence.infixRel )
      ctx += ( "ax", hos"x < y, y < z :- x < z" )
      val lk = ProofLink( le"ax 1 2 3", hos"1 < 2, 2 < 3 :- 1 < 3" )
      ctx.check( lk )

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate ProofLink multiple antecedents and succedents" in {
      implicit var ctx = Context.default
      ctx += Context.Sort( "i" )
      ctx += hoc"'<': i>i>o"
      ctx += hoc"'1': i"
      ctx += hoc"'2': i"
      ctx += hoc"'3': i"
      ctx += hoc"'ax': i>i>i>i>i"
      ctx += Notation.Infix( "<", Precedence.infixRel )
      ctx += ( "ax", hos"x < y, y < z :- x < z, x < a, a < a" )
      val lk = ProofLink( le"ax 1 1 2 3", hos"1 < 2, 2 < 3 :- 1 < 3, 1 < 1, 1 < 1" )
      ctx.check( lk )

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )
      checkEquality( nd, lk, focus )
    }

    "translate DefinitionLeftRule" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( DefinitionLeftRule( _, Ant( 0 ), hof"B" ) ).
        qed

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate DefinitionRightRule with main formula not focused" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( DefinitionRightRule( _, Suc( 1 ), hof"C" ) ).
        qed

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate DefinitionRightRule with main formula focused" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"A" ) ).
        u( WeakeningRightRule( _, hof"B" ) ).
        u( DefinitionRightRule( _, Suc( 1 ), hof"C" ) ).
        qed

      val focus = Some( Suc( 1 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate InductionRule with changing hypothesis index" in {
      val lk = examples.theories.nat.addcomm.proof

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate classical pairing" in {
      val p1 = LogicalAxiom( hof"x" )
      val p2 = LogicalAxiom( hof"y" )
      val p3 = BottomAxiom
      val p4 = ImpLeftRule( p2, Suc( 0 ), p3, Ant( 0 ) )
      val p5 = ImpLeftRule( p1, Suc( 0 ), p4, Ant( 0 ) )
      val p6 = WeakeningRightRule( p5, hof"⊥" )
      val p7 = ImpRightRule( p6, Ant( 0 ), Suc( 0 ) )
      val p8 = ImpRightRule( p7, Ant( 1 ), Suc( 0 ) )
      val p9 = ImpRightRule( p8, Ant( 0 ), Suc( 0 ) )
      val lk = p9

      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus )
    }

    "translate issue687 intuitionistically" in {
      import at.logic.gapt.proofs.gaptic._
      val lk = Proof( hols"A ∨ B, C → ¬B, C ⊢ A" ) {
        orL left trivial
        impL left trivial
        negL; trivial
      }
      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )
      checkEquality( nd, lk, focus )

      val containsEM = nd.treeLike.postOrder.exists {
        case _: ExcludedMiddleRule => true
        case _                     => false
      }
      containsEM mustEqual false
    }

    "translate issue688" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"P(x)" ) ).
        u( WeakeningLeftRule( _, hof"x=y" ) ).
        u( EqualityLeftRule( _, Ant( 0 ), Ant( 1 ), le"^x (P x: o)".asInstanceOf[Abs] ) ).
        qed
      val focus = Some( Suc( 0 ) )
      val nd = LKToND( lk, focus )
      checkEquality( nd, lk, focus )
    }
  }
}

