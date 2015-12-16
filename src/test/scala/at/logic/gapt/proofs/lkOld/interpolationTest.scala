package at.logic.gapt.proofs.lkOld

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.occurrences._
import org.specs2.mutable._
import at.logic.gapt.formats.prover9.Prover9TermParser.parseFormula
import at.logic.gapt.proofs.lkOld.base.OccSequent
import at.logic.gapt.provers.eqProver.EquationalProver

class interpolationTest extends Specification {
  "interpolation" should {

    "correctly interpolate an axiom with top" in {
      val p = FOLAtom( "p", Nil )
      val ax = Axiom( p :: Nil, p :: Nil )
      val npart = Set[FormulaOccurrence]()
      val ppart = Set( ax.root.antecedent( 0 ), ax.root.succedent( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )

      ipl must beEqualTo( Top() )
    }

    "correctly create an interpolating proof" in {
      val p = FOLAtom( "p", Nil )
      val ax = Axiom( p :: Nil, p :: Nil )
      val npart = Set( ax.root.antecedent( 0 ), ax.root.succedent( 0 ) )
      val ppart = Set[FormulaOccurrence]()
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( p :: Nil, p :: Bottom() :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )
    }

    "correctly interpolate a single unary inference with not p" in {
      val p = FOLAtom( "p", Nil )
      val q = FOLAtom( "q", Nil )
      val ax = Axiom( p :: Nil, p :: Nil )
      val pr = OrRight1Rule( ax, p, q )
      val npart = Set( pr.root.succedent( 0 ) )
      val ppart = Set( pr.root.antecedent( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( pr, npart, ppart )

      ipl must beEqualTo( Neg( p ) )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( Nil, Neg( p ) :: Or( p, q ) :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( p :: Neg( p ) :: Nil, Nil ) )
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

      ipl must beEqualTo( Or( Bottom(), q ) )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( Or( p, q ) :: Nil, p :: Or( Bottom(), q ) :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( Or( Bottom(), q ) :: Nil, q :: Nil ) )
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
      val p3 = ImpRightRule( p2, Neg( q ), r )
      val p4 = ImpLeftRule( axp, p3, p, Or( q, r ) )

      val npart = Set( p4.root.antecedent( 0 ), p4.root.antecedent( 1 ) )
      val ppart = Set( p4.root.succedent( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( p4, npart, ppart )

      ipl must beEqualTo( Or( Bottom(), Or( q, r ) ) )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( p :: Imp( p, Or( q, r ) ) :: Nil, Or( Bottom(), Or( q, r ) ) :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( Or( Bottom(), Or( q, r ) ) :: Nil, Imp( Neg( q ), r ) :: Nil ) )
    }

    "correctly interpolate a trivial atomic cut" in {
      val p = FOLAtom( "p", Nil )
      val q = FOLAtom( "q", Nil )
      val r = FOLAtom( "r", Nil )

      val axp = Axiom( p :: Nil, p :: Nil )
      val axp1 = Axiom( p :: Nil, p :: Nil )
      val p1 = CutRule( axp, axp1, p )

      val npart = Set( p1.root.antecedent( 0 ) )
      val ppart = Set( p1.root.succedent( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( p1, npart, ppart )

      val I = Or( Bottom(), p )

      ipl must beEqualTo( I )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( p :: Nil, I :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( I :: Nil, p :: Nil ) )
    }

    "correctly interpolate a trivial atomic cut (different partition)" in {
      val p = FOLAtom( "p", Nil )
      val q = FOLAtom( "q", Nil )
      val r = FOLAtom( "r", Nil )

      val axp = Axiom( p :: Nil, p :: Nil )
      val axp1 = Axiom( p :: Nil, p :: Nil )
      val p1 = CutRule( axp, axp1, p )

      val npart = Set( p1.root.antecedent( 0 ), p1.root.succedent( 0 ) )
      val ppart = Set.empty[FormulaOccurrence]

      val ( nproof, pproof, ipl ) = Interpolate( p1, npart, ppart )

      val I = Or( Bottom(), Bottom() )

      ipl must beEqualTo( I )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( p :: Nil, p :: I :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( I :: Nil, Nil ) )
    }

    "correctly interpolate a small proof with a single atomic cut" in {
      val p = FOLAtom( "p", Nil )
      val q = FOLAtom( "q", Nil )
      val r = FOLAtom( "r", Nil )

      val axp = Axiom( p :: Nil, p :: Nil )
      val axp1 = Axiom( p :: Nil, p :: Nil )
      val axq = Axiom( q :: Nil, q :: Nil )
      val axr = Axiom( r :: Nil, r :: Nil )
      val p1 = NegLeftRule( axq, q )
      val p2 = OrLeftRule( p1, axr, q, r )
      val p3 = ImpRightRule( p2, Neg( q ), r )
      val p4 = ImpLeftRule( axp, p3, p, Or( q, r ) )
      val p5 = WeakeningRightRule( p4, p )
      val p6 = CutRule( p5, axp1, p )

      val npart = Set( p6.root.antecedent( 0 ), p6.root.antecedent( 1 ) )
      val ppart = Set( p6.root.succedent( 0 ), p6.root.succedent( 1 ) )

      val ( nproof, pproof, ipl ) = Interpolate( p6, npart, ppart )

      val I = Or( Or( Bottom(), Or( q, r ) ), p )

      ipl must beEqualTo( I )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( p :: Imp( p, Or( q, r ) ) :: Nil, I :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( I :: Nil, Imp( Neg( q ), r ) :: p :: Nil ) )
    }

    "correctly interpolate another small proof with a single atomic cut" in {
      val p = FOLAtom( "p", Nil )
      val q = FOLAtom( "q", Nil )
      val r = FOLAtom( "r", Nil )

      val axp = Axiom( p :: Nil, p :: Nil )
      val axp1 = Axiom( p :: Nil, p :: Nil )
      val axq = Axiom( q :: Nil, q :: Nil )
      val axr = Axiom( r :: Nil, r :: Nil )
      val p1 = NegLeftRule( axq, q )
      val p2 = OrLeftRule( p1, axr, q, r )
      val p3 = ImpRightRule( p2, Neg( q ), r )
      val p4 = ImpLeftRule( axp, p3, p, Or( q, r ) )
      val p5 = WeakeningRightRule( p4, q )
      val p6 = WeakeningLeftRule( axp1, q )
      val p7 = CutRule( p5, p6, q )

      val npart = Set( p7.root.antecedent( 0 ), p7.root.antecedent( 1 ), p7.root.antecedent( 2 ) )
      val ppart = Set( p7.root.succedent( 0 ), p7.root.succedent( 1 ) )

      val ( nproof, pproof, ipl ) = Interpolate( p7, npart, ppart )

      val I = Or( Or( Bottom(), Or( q, r ) ), p )

      ipl must beEqualTo( I )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( p :: Imp( p, Or( q, r ) ) :: p :: Nil, I :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( I :: Nil, Imp( Neg( q ), r ) :: p :: Nil ) )
    }

    "correctly interpolate a proof with two atomic cuts" in {
      val p = FOLAtom( "p", Nil )

      val axp = Axiom( p :: Nil, p :: Nil )
      val axp1 = Axiom( p :: Nil, p :: Nil )
      val axp2 = Axiom( p :: Nil, p :: Nil )
      val axp3 = Axiom( p :: Nil, p :: Nil )

      val negp = Neg( p )
      val nnegp = Neg( negp )

      val p1 = NegRightRule( axp, p )
      val p2 = NegLeftRule( p1, negp )
      val p3 = WeakeningRightRule( p2, p )
      val p4 = ImpRightRule( p3, nnegp, p )

      val p5 = NegLeftRule( axp2, p )
      val p6 = WeakeningRightRule( p5, p )
      val p7 = OrLeftRule( axp1, p6, p, negp )
      val p8 = ContractionRightRule( p7, p )

      val p9 = WeakeningLeftRule( axp3, nnegp )
      val p10 = ImpRightRule( p9, nnegp, p )
      val p11 = CutRule( p8, p10, p )

      val p12 = CutRule( p4, p11, p )

      val p13 = ContractionRightRule( p12, Imp( nnegp, p ) )

      val npart = Set( p13.root.antecedent( 0 ) )
      val ppart = Set( p13.root.succedent( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( p13, npart, ppart )

      val I = Or( Top(), Or( Or( Bottom(), Bottom() ), p ) )

      ipl must beEqualTo( I )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( Or( p, Neg( p ) ) :: Nil, I :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( I :: Nil, Imp( Neg( Neg( p ) ), p ) :: Nil ) )
    }

    "correctly interpolate a proof with two cuts and two equality right rules" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = Axiom( pa )
      val axpb = Axiom( pb )
      val axab1 = Axiom( aeqb )
      val axab2 = Axiom( aeqb )
      val axab3 = Axiom( aeqb )
      val axab4 = Axiom( aeqb )

      val p1 = EquationRight1Rule( axab1, axpa, axab1.root.succedent.head, axpa.root.succedent.head, pb )

      val p2 = CutRule( axab2, p1, aeqb )
      val p3 = ImpRightRule( p2, pa, pb )

      val p4 = EquationRight2Rule( axab3, axpb, axab3.root.succedent.head, axpb.root.succedent.head, pa )

      val p5 = CutRule( axab4, p4, aeqb )
      val p6 = ImpRightRule( p5, pb, pa )

      val p7 = AndRightRule( p3, p6, Imp( pa, pb ), Imp( pb, pa ) )
      val p8 = ContractionLeftRule( p7, aeqb )
      val p9 = ImpRightRule( p8, aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) )

      val npart = Set( p9.root.succedent( 0 ) )
      val ppart = Set.empty[FormulaOccurrence]

      val ( nproof, pproof, ipl ) = Interpolate( p9, npart, ppart )

      val Il = Or( Bottom(), Or( Bottom(), And( aeqb, Bottom() ) ) )
      val Ir = Or( Bottom(), Or( Bottom(), And( aeqb, Bottom() ) ) )
      val I = Or( Il, Ir )

      ipl must beEqualTo( I )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( Nil, List( I, Imp( aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) ) ) ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( List( I ), Nil ) )
    }

    "correctly interpolate a proof with two cuts and two equality right rules (different partition)" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = Axiom( pa )
      val axpb = Axiom( pb )
      val axab1 = Axiom( aeqb )
      val axab2 = Axiom( aeqb )
      val axab3 = Axiom( aeqb )
      val axab4 = Axiom( aeqb )

      val p1 = EquationRight1Rule( axab1, axpa, axab1.root.succedent.head, axpa.root.succedent.head, pb )

      val p2 = CutRule( axab2, p1, aeqb )
      val p3 = ImpRightRule( p2, pa, pb )

      val p4 = EquationRight2Rule( axab3, axpb, axab3.root.succedent.head, axpb.root.succedent.head, pa )

      val p5 = CutRule( axab4, p4, aeqb )
      val p6 = ImpRightRule( p5, pb, pa )

      val p7 = AndRightRule( p3, p6, Imp( pa, pb ), Imp( pb, pa ) )
      val p8 = ContractionLeftRule( p7, aeqb )
      val p9 = ImpRightRule( p8, aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) )

      val npart = Set.empty[FormulaOccurrence]
      val ppart = Set( p9.root.succedent( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( p9, npart, ppart )

      val Il = And( Top(), Or( Neg( aeqb ), And( aeqb, Top() ) ) )
      val Ir = And( Top(), Or( Neg( aeqb ), And( aeqb, Top() ) ) )
      val I = And( Il, Ir )

      ipl must beEqualTo( I )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( Nil, List( I ) ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( List( I ), List( Imp( aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) ) ) ) )
    }

    "correctly interpolate a proof with two cuts and two equality left rules" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = Axiom( pa )
      val axpb = Axiom( pb )
      val axab1 = Axiom( aeqb )
      val axab2 = Axiom( aeqb )
      val axab3 = Axiom( aeqb )
      val axab4 = Axiom( aeqb )

      val p1 = EquationLeft2Rule( axab1, axpb, axab1.root.succedent.head, axpb.root.antecedent.head, pa )

      val p2 = CutRule( axab2, p1, aeqb )
      val p3 = ImpRightRule( p2, pa, pb )

      val p4 = EquationLeft1Rule( axab3, axpa, axab3.root.succedent.head, axpa.root.antecedent.head, pb )

      val p5 = CutRule( axab4, p4, aeqb )
      val p6 = ImpRightRule( p5, pb, pa )

      val p7 = AndRightRule( p3, p6, Imp( pa, pb ), Imp( pb, pa ) )
      val p8 = ContractionLeftRule( p7, aeqb )
      val p9 = ImpRightRule( p8, aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) )

      val npart = Set( p9.root.succedent( 0 ) )
      val ppart = Set.empty[FormulaOccurrence]

      val ( nproof, pproof, ipl ) = Interpolate( p9, npart, ppart )

      val Il = Or( Bottom(), And( aeqb, Imp( aeqb, Bottom() ) ) )
      val Ir = Or( Bottom(), And( aeqb, Imp( aeqb, Bottom() ) ) )
      val I = Or( Il, Ir )

      ipl must beEqualTo( I )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( Nil, List( I, Imp( aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) ) ) ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( List( I ), Nil ) )
    }

    "correctly interpolate a proof with two cuts and two equality left rules (different partition)" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val pa = FOLAtom( "P", List( a ) )
      val pb = FOLAtom( "P", List( b ) )
      val aeqb = Eq( a, b )

      val axpa = Axiom( pa )
      val axpb = Axiom( pb )
      val axab1 = Axiom( aeqb )
      val axab2 = Axiom( aeqb )
      val axab3 = Axiom( aeqb )
      val axab4 = Axiom( aeqb )

      val p1 = EquationLeft2Rule( axab1, axpb, axab1.root.succedent.head, axpb.root.antecedent.head, pa )

      val p2 = CutRule( axab2, p1, aeqb )
      val p3 = ImpRightRule( p2, pa, pb )

      val p4 = EquationLeft1Rule( axab3, axpa, axab3.root.succedent.head, axpa.root.antecedent.head, pb )

      val p5 = CutRule( axab4, p4, aeqb )
      val p6 = ImpRightRule( p5, pb, pa )

      val p7 = AndRightRule( p3, p6, Imp( pa, pb ), Imp( pb, pa ) )
      val p8 = ContractionLeftRule( p7, aeqb )
      val p9 = ImpRightRule( p8, aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) )

      val npart = Set.empty[FormulaOccurrence]
      val ppart = Set( p9.root.succedent( 0 ) )

      val ( nproof, pproof, ipl ) = Interpolate( p9, npart, ppart )

      val Il = And( Top(), And( Top(), Top() ) )
      val Ir = And( Top(), And( Top(), Top() ) )
      val I = And( Il, Ir )

      ipl must beEqualTo( I )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( Nil, List( I ) ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( List( I ), List( Imp( aeqb, And( Imp( pa, pb ), Imp( pb, pa ) ) ) ) ) )
    }

    "correctly interpolate an axiom of the form Bottom() :- " in {
      val ax = Axiom( Bottom() :: Nil, Nil )

      val npart = Set( ax.root.antecedent( 0 ) )
      val ppart = Set.empty[FormulaOccurrence]

      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Bottom() :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )

      val ( nproof2, pproof2, ipl2 ) = Interpolate( ax, ppart, npart )

      ipl2 must beEqualTo( Top() )
      nproof2.root.toHOLSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof2.root.toHOLSequent must beEqualTo( HOLSequent( Bottom() :: Top() :: Nil, Nil ) )
    }

    "correctly interpolate an axiom of the form :- Top()" in {
      val ax = Axiom( Nil, Top() :: Nil )

      val npart = Set( ax.root.succedent( 0 ) )
      val ppart = Set.empty[FormulaOccurrence]

      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )

      ipl must beEqualTo( Bottom() )
      nproof.root.toHOLSequent must beEqualTo( HOLSequent( Nil, Top() :: Bottom() :: Nil ) )
      pproof.root.toHOLSequent must beEqualTo( HOLSequent( Bottom() :: Nil, Nil ) )

      val ( nproof2, pproof2, ipl2 ) = Interpolate( ax, ppart, npart )

      ipl2 must beEqualTo( Top() )
      nproof2.root.toHOLSequent must beEqualTo( HOLSequent( Nil, Top() :: Nil ) )
      pproof2.root.toHOLSequent must beEqualTo( HOLSequent( Top() :: Nil, Top() :: Nil ) )
    }

  }
}
