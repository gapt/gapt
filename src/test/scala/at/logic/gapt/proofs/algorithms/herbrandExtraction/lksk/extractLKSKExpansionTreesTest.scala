package at.logic.gapt.proofs.algorithms.herbrandExtraction.lksk

import org.specs2.mutable._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lksk
import at.logic.gapt.proofs.expansionTrees.{ ETAtom, ETNeg, ETSkolemQuantifier, ExpansionTree, ExpansionSequent, ETWeakQuantifier, ETImp }
import at.logic.gapt.proofs.lksk.LabelledFormulaOccurrence
import at.logic.gapt.proofs.algorithms.skolemization.lksk.{ LKtoLKskc => skolemize }

/**
 * Created by marty on 8/7/14.
 */
class extractLKSKExpansionSequentTest extends Specification {
  object simpleHOLProof {
    val p = HOLAtom( Const( "P", To ), Nil )
    val x = Var( "X", To )
    val xatom = HOLAtom( x, Nil )
    val existsx = Ex( x, xatom )

    val ax = Axiom( List( p ), List( p ) )
    val i1 = ExistsRightRule( ax, ax.root.succedent( 0 ), existsx, p )
    val i2 = NegRightRule( i1, i1.root.antecedent( 0 ) )
    val i3 = ExistsRightRule( i2, i2.root.succedent( 1 ), existsx, Neg( p ) )
    val i4 = ContractionRightRule( i3, i3.root.succedent( 0 ), i3.root.succedent( 1 ) )
    val proof = skolemize( i4 )
  }

  object simpleLKSKProof {
    val p = HOLAtom( Const( "P", To ), Nil )
    val x = Var( "X", To )
    val xatom = HOLAtom( x, Nil )
    val existsx = Ex( x, xatom )

    val ( ax, _ ) = lksk.Axiom.createDefault( FSequent( List( p ), List( p ) ), ( List( Set( Neg( p ) ) ), List( Set( p ) ) ) )
    val i1 = lksk.ExistsSkRightRule( ax, ax.root.succedent( 0 ).asInstanceOf[LabelledFormulaOccurrence], existsx, p, true )
    val i2 = NegRightRule( i1, i1.root.antecedent( 0 ) )
    val i3 = lksk.ExistsSkRightRule( i2, i2.root.succedent( 1 ).asInstanceOf[LabelledFormulaOccurrence], existsx, Neg( p ), true )
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

    val ax = Axiom( List( pa ), List( pa ) )
    val i1 = ExistsRightRule( ax, ax.root.succedent( 0 ), existsx, Abs( u, pu ) )
    val i2 = NegRightRule( i1, i1.root.antecedent( 0 ) )
    val i3 = ExistsRightRule( i2, i2.root.succedent( 1 ), existsx, Abs( u, Neg( pu ) ) )
    val i4 = ContractionRightRule( i3, i3.root.succedent( 0 ), i3.root.succedent( 1 ) )
    val i5 = ForallRightRule( i4, i4.root.succedent( 0 ), alluexistsx, a )

    val proof = skolemize( i5 )
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

    val ax = Axiom( List( pa ), List( pa ) )
    val i0a = ForallLeftRule( ax, ax.root.antecedent( 0 ), allpu, a )
    val i0b = ForallRightRule( i0a, i0a.root.succedent( 0 ), allpu, a )
    val i1 = ExistsRightRule( i0b, i0b.root.succedent( 0 ), existsx, allpu )
    val i2 = NegRightRule( i1, i1.root.antecedent( 0 ) )
    val i3 = ExistsRightRule( i2, i2.root.succedent( 1 ), existsx, Neg( allpu ) )
    val i4 = ContractionRightRule( i3, i3.root.succedent( 0 ), i3.root.succedent( 1 ) )
    val proof = skolemize( i4 )
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

    val ax = Axiom( List( pa ), List( pa ) )
    val i0a = ForallLeftRule( ax, ax.root.antecedent( 0 ), allpu, a )
    val i0b = ForallRightRule( i0a, i0a.root.succedent( 0 ), allpu, a )
    val i1 = ExistsRightRule( i0b, i0b.root.succedent( 0 ), existsx, allpu )
    val i2 = NegRightRule( i1, i1.root.antecedent( 0 ) )
    val i2a = WeakeningLeftRule( i2, allpu )
    val i2b = ImpRightRule( i2a, i2a.root.antecedent( 0 ), i2a.root.succedent( 1 ) )
    val i3 = ExistsRightRule( i2b, i2b.root.succedent( 1 ), existsx, Imp( allpu, Neg( allpu ) ) )
    val i4 = ContractionRightRule( i3, i3.root.succedent( 0 ), i3.root.succedent( 1 ) )
    val proof = skolemize( i4 )
  }

  "LKSK Expansion Tree Extraction" should {
    "work for an hol proof with only weak quantifiers" in {

      val et = extractLKSKExpansionSequent( simpleHOLProof.i4, false )

      val inst1: ( ExpansionTree, HOLFormula ) = ( ETAtom( simpleHOLProof.p ), simpleHOLProof.p )
      val inst2: ( ExpansionTree, HOLFormula ) = ( ETNeg( ETAtom( simpleHOLProof.p ) ), Neg( simpleHOLProof.p ) )
      val cet: ExpansionTree = ETWeakQuantifier( simpleHOLProof.existsx, List( inst1, inst2 ) ).asInstanceOf[ExpansionTree] //TODO: this cast is ugly

      val control = ExpansionSequent( Nil, List( cet ) )

      et must_== ( control )
    }

    "work for the same hol proof, automatically skolemized" in {
      val ExpansionSequent( ( Nil, List( et ) ) ) = extractLKSKExpansionSequent( simpleHOLProof.proof, false )

      val r = et match {
        case ETWeakQuantifier( _, Seq(
          ( ETAtom( _ ), _ ),
          ( ETNeg( ETAtom( _ ) ), _ ) )
          ) =>
          ""
        case _ =>
          "expansion tree " + et + " does not match expected pattern!"
      }

      r must_== ( "" )
    }

    "work for the same hol proof, manually skolemized" in {
      val ExpansionSequent( ( Nil, List( et ) ) ) = extractLKSKExpansionSequent( simpleLKSKProof.i4, false )

      val r = et match {
        case ETWeakQuantifier( _, Seq(
          ( ETAtom( _ ), _ ),
          ( ETNeg( ETAtom( _ ) ), _ ) )
          ) =>
          ""
        case _ =>
          "expansion tree " + et + " does not match expected pattern!"
      }

      r must_== ( "" )
    }

    "work for a skolemized hol proof with strong individual quantifiers" in {
      val ExpansionSequent( ( Nil, List( et ) ) ) = extractLKSKExpansionSequent( simpleHOLProof2.proof, false )

      val r = et match {
        case ETSkolemQuantifier( _, sk,
          ETWeakQuantifier( _, Seq(
            ( ETAtom( _ ), _ ),
            ( ETNeg( ETAtom( _ ) ), _ ) )
            ) ) =>
          ""
        case _ =>
          "expansion tree " + et + " does not match expected pattern!"
      }

      r must_== ( "" )
    }

    "work for a skolemized hol proof with strong individual quantifiers inside weak ho quantifiers" in {
      val ExpansionSequent( ( Nil, List( et ) ) ) = extractLKSKExpansionSequent( simpleHOLProof3.proof, false )

      val r = et match {
        case ETWeakQuantifier( _, Seq(
          ( ETSkolemQuantifier( _, sk1, ETAtom( _ ) ), _ ),
          ( ETNeg( ETWeakQuantifier( _, Seq( ( ETAtom( _ ), sk2 ) ) ) ), _ )
          ) ) =>
          ""
        case _ =>
          "expansion tree " + et + " does not match expected pattern!"
      }

      r must_== ( "" )
    }

    "work for a skolemized hol proof with weakening" in {
      val ExpansionSequent( ( Nil, List( et ) ) ) = extractLKSKExpansionSequent( simpleHOLProof4.proof, false )

      val r = et match {
        case ETWeakQuantifier( _, Seq(
          ( ETSkolemQuantifier( _, sk1, ETAtom( _ ) ), _ ),
          ( ETImp( ETAtom( _ ), ETNeg( ETWeakQuantifier( _, Seq( ( ETAtom( _ ), sk2 ) ) ) ) ), _ )
          ) ) =>
          ""
        case _ =>
          "expansion tree " + et + " does not match expected pattern!"
      }

      r must_== ( "" )
    }
  }

}
