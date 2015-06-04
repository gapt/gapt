/*
 * LKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.proofs.algorithms.skolemization.lksk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.lk.base.{ LKProof, Sequent }
import at.logic.gapt.proofs.lk.{ OrLeftRule, Axiom => LKAxiom }
import at.logic.gapt.proofs.lk.{ ForallLeftRule, ForallRightRule, ExistsLeftRule, ExistsRightRule }
import at.logic.gapt.proofs.lksk._
import org.specs2.mutable._
import at.logic.gapt.proofs.lksk.TypeSynonyms.EmptyLabel

class LKskcTest extends Specification {

  "Transformation from LK to LKskc" should {
    val x = Var( "x", Ti )
    val y = Var( "y", Ti )
    val c = Const( "c", Ti )
    val r = Const( "R", Ti -> ( Ti -> To ) )

    "work for a small proof with only weak quantifiers" in {
      val Rcc = HOLAtom( r, c :: c :: Nil )
      val Rcx = HOLAtom( r, c :: x :: Nil )
      val Ryx = HOLAtom( r, y :: x :: Nil )
      val allxRcx = All( x, Rcx )
      val allyallxRyx = All( y, All( x, Ryx ) )
      val proof = ForallLeftRule(
        ForallLeftRule(
          LKAxiom( Rcc :: Nil, Nil ),
          Rcc, allxRcx, c ),
        allxRcx, allyallxRyx, c )
      val lkskc_proof = LKtoLKskc( proof, Set() )

      lkskc_proof.root.antecedent.toList.head must beLike {
        case o: LabelledFormulaOccurrence =>
          o.skolem_label == EmptyLabel() && o.formula == proof.root.antecedent.head.formula must_== true
      }
    }

    "work for a cut-free proof" in {
      val a = Var( "a", Ti )
      val b = Var( "b", Ti )
      val Rab = HOLAtom( r, a :: b :: Nil )
      val exyRay = Ex( y, HOLAtom( r, a :: y :: Nil ) )
      val allxexyRxy = All( x, Ex( y, HOLAtom( r, x :: y :: Nil ) ) )
      val ax = LKAxiom( Rab :: Nil, Rab :: Nil )
      val r1 = ExistsRightRule( ax, Rab, exyRay, b )
      val r2 = ExistsLeftRule( r1, Rab, exyRay, b )
      val r3 = ForallLeftRule( r2, exyRay, allxexyRxy, a )
      val r4 = ForallRightRule( r3, exyRay, allxexyRxy, a )
      val lkskc_proof = LKtoLKskc( r4, Set() )

      val occurrences: Set[FormulaOccurrence] = lkskc_proof.nodes.flatMap( x => x.asInstanceOf[LKProof].root.occurrences ).toSet
      val constants = occurrences.flatMap( x => subTerms( x.formula ).filter( _ match { case VarOrConst( _, _ ) => true; case _ => false } ) )
      println( constants )

      lkskc_proof.root.antecedent.toList.head must beLike {
        case o: LabelledFormulaOccurrence =>
          o.skolem_label == EmptyLabel() && o.formula == r4.root.antecedent.head.formula must_== true
      }
    }
  }
}
