/*
 * LKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.skolemization.lksk

import at.logic.language.hol._
import at.logic.language.lambda.symbols._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.calculi.lk.{OrLeftRule, Axiom => LKAxiom}
import at.logic.calculi.lk.{ForallLeftRule, ForallRightRule, ExistsLeftRule, ExistsRightRule}
import at.logic.calculi.lksk._
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.types._
import at.logic.calculi.lksk.TypeSynonyms.EmptyLabel

@RunWith(classOf[JUnitRunner])
class LKskcTest extends SpecificationWithJUnit {

  "Transformation from LK to LKskc" should {
    val x = HOLVar("x", Ti)
    val y = HOLVar("y", Ti)
    val c = HOLConst("c", Ti)
    val r = HOLConst("R", Ti -> (Ti -> To))

    "work for a small proof with only weak quantifiers" in {
      val Rcc = Atom(r, c::c::Nil)
      val Rcx = Atom(r, c::x::Nil)
      val Ryx = Atom(r, y::x::Nil)
      val allxRcx = AllVar( x, Rcx )
      val allyallxRyx = AllVar( y, AllVar( x, Ryx ) )
      val proof = ForallLeftRule( 
                    ForallLeftRule( 
                      LKAxiom( Rcc::Nil, Nil ),
                    Rcc, allxRcx, c ),
                  allxRcx, allyallxRyx, c )
      val lkskc_proof = LKtoLKskc( proof, Set())

      lkskc_proof.root.antecedent.toList.head must beLike {
        case o : LabelledFormulaOccurrence =>
          o.skolem_label == EmptyLabel() && o.formula == proof.root.antecedent.head.formula must_== true
      }
    }

    "work for a cut-free proof" in {
      val a = HOLVar("a", Ti)
      val b = HOLVar("b", Ti)
      val Rab = Atom( r, a::b::Nil )
      val exyRay = ExVar( y, Atom( r, a::y::Nil ) )
      val allxexyRxy = AllVar( x, ExVar( y, Atom( r, x::y::Nil ) ) )
      val ax = LKAxiom( Rab::Nil, Rab::Nil  )
      val r1 = ExistsRightRule( ax, Rab, exyRay, b )
      val r2 = ExistsLeftRule( r1, Rab, exyRay, b )
      val r3 = ForallLeftRule( r2, exyRay, allxexyRxy, a )
      val r4 = ForallRightRule( r3, exyRay, allxexyRxy, a )
      val lkskc_proof = LKtoLKskc( r4, Set() )

      val occurrences : Set[FormulaOccurrence] = lkskc_proof.nodes.flatMap(x => x.asInstanceOf[LKProof].root.occurrences).toSet
      val constants = occurrences.flatMap(x => subTerms(x.formula).filter(_ match { case VarOrConst(_,_) => true; case _ => false }))
      println(constants)

      lkskc_proof.root.antecedent.toList.head must beLike{
        case o : LabelledFormulaOccurrence =>
          o.skolem_label == EmptyLabel() && o.formula == r4.root.antecedent.head.formula must_== true
      }
    } 
  }
}
