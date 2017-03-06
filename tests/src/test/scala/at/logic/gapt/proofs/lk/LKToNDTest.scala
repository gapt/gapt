package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.nd.NDProof
import at.logic.gapt.proofs.{ Ant, SequentIndex, SequentMatchers, Suc }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class LKToNDTest extends Specification with SatMatchers with SequentMatchers {

  def checkEquality( nd: NDProof, lk: LKProof, focus: SequentIndex ) = {
    lk.endSequent.size == nd.endSequent.size &&
      lk.endSequent.succedent.contains( nd.endSequent( Suc( 0 ) ) ) &&
      lk.endSequent.antecedent.forall( nd.endSequent.antecedent.contains( _ ) ) &&
      lk.endSequent.succedent.filter( _ != nd.endSequent( Suc( 0 ) ) ).forall( x => nd.endSequent.antecedent.contains( Neg( x ) ) )
  }

  "The LK to ND translation" should {

    /*
    "translate DeMorgan's law" in {
    }
    */

    "translate OrLeft 1" in {
      val l1 = LogicalAxiom( hof"A" )
      val r1 = LogicalAxiom( hof"B" )
      val lk = OrLeftRule( l1, r1, hof"A | B" )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrLeft 2" in {
      val l1 = LogicalAxiom( hof"A" )
      val r1 = LogicalAxiom( hof"A" )
      val lk = OrLeftRule( l1, r1, hof"A | A" )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrLeft 3" in {
      val l1 = LogicalAxiom( hof"A" )
      val r1 = LogicalAxiom( hof"B" )
      val r2 = WeakeningRightRule( r1, hof"C" )
      val r3 = WeakeningLeftRule( r2, hof"D" )
      val lk = OrLeftRule( l1, r3, hof"A | D" )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrLeft 4 with focus 3" in {
      val l1 = LogicalAxiom( hof"A" )
      val l2 = WeakeningRightRule( l1, hof"C" )
      val r1 = LogicalAxiom( hof"B" )
      val r2 = WeakeningRightRule( r1, hof"C" )
      val r3 = WeakeningLeftRule( r2, hof"D" )
      val lk = OrLeftRule( l2, r3, hof"A | D" )

      val focus = Suc( 3 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrLeft 5 with focus 2" in {
      val l1 = LogicalAxiom( hof"A" )
      val l2 = WeakeningLeftRule( l1, hof"A" )
      val l3 = NegRightRule( l2, hof"A" )
      val r1 = LogicalAxiom( hof"B" )
      val r2 = WeakeningRightRule( r1, hof"B" )
      val lk = OrLeftRule( l3, r2, hof"A | B" )

      val focus = Suc( 2 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate ImpRight 1 with focus 1" in {
      val p1 = LogicalAxiom( hof"A" )
      val p2 = WeakeningRightRule( p1, hof"B" )
      val lk = ImpRightRule( p2, hof"A -> B" )

      val focus = Suc( 1 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate ImpRight 2" in {
      val p1 = LogicalAxiom( hof"A" )
      val p2 = WeakeningRightRule( p1, hof"B" )
      val lk = ImpRightRule( p2, hof"A -> B" )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrRight 1" in {
      val r1 = LogicalAxiom( hof"A" )
      val r2 = WeakeningRightRule( r1, hof"B" )
      val lk = OrRightRule( r2, hof"A | B" )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate OrRight 2" in {
      val p1 = LogicalAxiom( hof"A" )
      val p2 = WeakeningLeftRule( p1, hof"B" )
      val p3 = NegRightRule( p2, hof"B" )
      val lk = OrRightRule( p3, hof"A | -B" )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate NegLeft followed by NegRight" in {
      val p1 = LogicalAxiom( hof"A" )
      val p2 = NegLeftRule( p1, hof"A" )
      val lk = NegRightRule( p2, hof"-A" )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate NegRight" in {
      val p1 = LogicalAxiom( hof"A" )
      val p2 = WeakeningLeftRule( p1, hof"B" )
      val lk = NegRightRule( p2, hof"B" )

      val focus = Suc( 0 )
      val nd = LKToND( lk )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate WeakeningRight followed by ContractRight" in {
      val p1 = LogicalAxiom( hof"A" )
      val p2 = WeakeningRightRule( p1, hof"A" )
      val lk = ContractionRightRule( p2, hof"A" )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate Cut 1" in {
      val p1 = LogicalAxiom( hof"A" )
      val p2 = LogicalAxiom( hof"A" )
      val lk = CutRule( p1, Suc( 0 ), p2, Ant( 0 ) )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }

    "translate Cut 2" in {
      val l1 = LogicalAxiom( hof"A" )
      val l2 = WeakeningLeftRule( l1, hof"B" )
      val r1 = LogicalAxiom( hof"A" )
      val r2 = WeakeningRightRule( r1, hof"C" )
      val lk = CutRule( l2, Suc( 0 ), r2, Ant( 0 ) )

      val focus = Suc( 0 )
      val nd = LKToND( lk, focus )

      checkEquality( nd, lk, focus ) mustEqual true
    }
  }
}

