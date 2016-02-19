package at.logic.gapt.proofs.lksk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.{ Sequent, HOLSequent }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lkOld.{ Axiom => LKAxiom, WeakeningLeftRule => LKWeakeningLeftRule, _ }
import at.logic.gapt.utils.SortedMap
import org.specs2.mutable._

/**
 * Created by marty on 8/7/14.
 */
class LKskToExpansionProofTest extends Specification {
  object simpleHOLProof {
    val p = HOLAtom( Const( "P", To ), Nil )
    val x = Var( "X", To )
    val xatom = HOLAtom( x, Nil )
    val existsx = Ex( x, xatom )

    val ax = LKAxiom( List( p ), List( p ) )
    val i1 = ExistsRightRule( ax, ax.root.succedent( 0 ), existsx, p )
    val i2 = NegRightRule( i1, i1.root.antecedent( 0 ) )
    val i3 = ExistsRightRule( i2, i2.root.succedent( 1 ), existsx, Neg( p ) )
    val i4 = ContractionRightRule( i3, i3.root.succedent( 0 ), i3.root.succedent( 1 ) )
    val proof = LKToLKsk( i4 )
  }

  object simpleLKskProof {
    val p = HOLAtom( Const( "P", To ), Nil )
    val x = Var( "X", To )
    val xatom = HOLAtom( x, Nil )
    val existsx = Ex( x, xatom )

    val ( ax, _ ) = Axiom.createDefault( HOLSequent( List( p ), List( p ) ), ( List( Set( Neg( p ) ) ), List( Set( p ) ) ) )
    val i1 = ExistsSkRightRule( ax, ax.root.succedent( 0 ).asInstanceOf[LabelledFormulaOccurrence], existsx, p, true )
    val i2 = NegRightRule( i1, i1.root.antecedent( 0 ) )
    val i3 = ExistsSkRightRule( i2, i2.root.succedent( 1 ).asInstanceOf[LabelledFormulaOccurrence], existsx, Neg( p ), true )
    val i4 = ContractionRightRule( i3, i3.root.succedent( 0 ), i3.root.succedent( 1 ) )
  }

  object simpleHOLProof2 {
    val x = Var( "X", Ti -> To )
    val a = Var( "\\alpha", Ti )
    val u = Var( "u", Ti )

    val p = Const( "P", Ti -> To )
    val pa = HOLAtom( p, List( a ) )
    val pu = HOLAtom( p, List( u ) )
    val xatoma = HOLAtom( x, List( a ) )
    val xatomu = HOLAtom( x, List( u ) )

    val existsx = Ex( x, xatoma )
    val alluexistsx = All( u, Ex( x, xatomu ) )

    val ax = LKAxiom( List( pa ), List( pa ) )
    val i1 = ExistsRightRule( ax, ax.root.succedent( 0 ), existsx, Abs( u, pu ) )
    val i2 = NegRightRule( i1, i1.root.antecedent( 0 ) )
    val i3 = ExistsRightRule( i2, i2.root.succedent( 1 ), existsx, Abs( u, Neg( pu ) ) )
    val i4 = ContractionRightRule( i3, i3.root.succedent( 0 ), i3.root.succedent( 1 ) )
    val i5 = ForallRightRule( i4, i4.root.succedent( 0 ), alluexistsx, a )

    val proof = LKToLKsk( i5 )
  }

  object simpleHOLProof3 {
    val p = Const( "P", Ti -> To )
    val a = Var( "\\alpha", Ti )
    val u = Var( "u", Ti )

    val pa = HOLAtom( p, a :: Nil )
    val pu = HOLAtom( p, u :: Nil )
    val allpu = All( u, pu )

    val x = Var( "X", To )
    val xatom = HOLAtom( x, Nil )
    val existsx = Ex( x, xatom )

    val ax = LKAxiom( List( pa ), List( pa ) )
    val i0a = ForallLeftRule( ax, ax.root.antecedent( 0 ), allpu, a )
    val i0b = ForallRightRule( i0a, i0a.root.succedent( 0 ), allpu, a )
    val i1 = ExistsRightRule( i0b, i0b.root.succedent( 0 ), existsx, allpu )
    val i2 = NegRightRule( i1, i1.root.antecedent( 0 ) )
    val i3 = ExistsRightRule( i2, i2.root.succedent( 1 ), existsx, Neg( allpu ) )
    val i4 = ContractionRightRule( i3, i3.root.succedent( 0 ), i3.root.succedent( 1 ) )
    val proof = LKToLKsk( i4 )
  }

  object simpleHOLProof4 {
    val p = Const( "P", Ti -> To )
    val a = Var( "\\alpha", Ti )
    val u = Var( "u", Ti )

    val pa = HOLAtom( p, a :: Nil )
    val pu = HOLAtom( p, u :: Nil )
    val allpu = All( u, pu )

    val x = Var( "X", To )
    val xatom = HOLAtom( x, Nil )
    val existsx = Ex( x, xatom )

    val ax = LKAxiom( List( pa ), List( pa ) )
    val i0a = ForallLeftRule( ax, ax.root.antecedent( 0 ), allpu, a )
    val i0b = ForallRightRule( i0a, i0a.root.succedent( 0 ), allpu, a )
    val i1 = ExistsRightRule( i0b, i0b.root.succedent( 0 ), existsx, allpu )
    val i2 = NegRightRule( i1, i1.root.antecedent( 0 ) )
    val i2a = LKWeakeningLeftRule( i2, allpu )
    val i2b = ImpRightRule( i2a, i2a.root.antecedent( 0 ), i2a.root.succedent( 1 ) )
    val i3 = ExistsRightRule( i2b, i2b.root.succedent( 1 ), existsx, Imp( allpu, Neg( allpu ) ) )
    val i4 = ContractionRightRule( i3, i3.root.succedent( 0 ), i3.root.succedent( 1 ) )
    val proof = LKToLKsk( i4 )
  }

  "LKsk Expansion Tree Extraction" should {
    "work for an hol proof with only weak quantifiers" in {

      val et = LKskToExpansionProof( simpleHOLProof.i4 )

      val inst1 = simpleHOLProof.p -> ETAtom( simpleHOLProof.p, true )
      val inst2 = -simpleHOLProof.p -> ETNeg( ETAtom( simpleHOLProof.p, false ) )
      val cet = ETWeakQuantifier( simpleHOLProof.existsx, Map( inst1, inst2 ) )

      et must_== ExpansionProof( Sequent() :+ cet )
    }

    "work for the same hol proof, automatically skolemized" in {
      val ExpansionProof( ExpansionSequent( ( Nil, List( et ) ) ) ) = LKskToExpansionProof( simpleHOLProof.proof )

      et must beLike {
        case ETWeakQuantifier( _, SortedMap(
          ( _, ETAtom( _, _ ) ),
          ( _, ETNeg( ETAtom( _, _ ) ) ) )
          ) => ok
      }
    }

    "work for the same hol proof, manually skolemized" in {
      val ExpansionProof( ExpansionSequent( ( Nil, List( et ) ) ) ) = LKskToExpansionProof( simpleLKskProof.i4 )

      et must beLike {
        case ETWeakQuantifier( _, SortedMap(
          ( _, ETAtom( _, _ ) ),
          ( _, ETNeg( ETAtom( _, _ ) ) ) )
          ) => ok
      }
    }

    "work for a skolemized hol proof with strong individual quantifiers" in {
      val ExpansionProof( ExpansionSequent( ( Nil, List( et ) ) ) ) = LKskToExpansionProof( simpleHOLProof2.proof )

      et must beLike {
        case ETSkolemQuantifier( _, sk,
          ETWeakQuantifier( _, SortedMap(
            ( _, ETAtom( _, _ ) ),
            ( _, ETNeg( ETAtom( _, _ ) ) ) )
            ) ) => ok
      }
    }

    "work for a skolemized hol proof with strong individual quantifiers inside weak ho quantifiers" in {
      val ExpansionProof( ExpansionSequent( ( Nil, List( et ) ) ) ) = LKskToExpansionProof( simpleHOLProof3.proof )

      et must beLike {
        case ETWeakQuantifier( _, SortedMap(
          ( _, ETNeg( ETWeakQuantifier( _, SortedMap( ( sk2, ETAtom( _, _ ) ) ) ) ) ),
          ( _, ETSkolemQuantifier( _, sk1, ETAtom( _, _ ) ) )
          ) ) => ok
      }
    }

    "work for a skolemized hol proof with weakening" in {
      val ExpansionProof( ExpansionSequent( ( Nil, List( et ) ) ) ) = LKskToExpansionProof( simpleHOLProof4.proof )

      et must beLike {
        case ETWeakQuantifier( _, SortedMap(
          ( _, ETImp( ETWeakening( _, _ ), ETNeg( ETWeakQuantifier( _, SortedMap( ( sk2, ETAtom( _, _ ) ) ) ) ) ) ),
          ( _, ETSkolemQuantifier( _, sk1, ETAtom( _, _ ) ) )
          ) ) => ok
      }
    }
  }

}
