/*
 * LKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.skolemization.lksk

import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols._
import at.logic.calculi.lksk.base._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules.{OrLeftRule, Axiom => LKAxiom}
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lksk.base.TypeSynonyms._
import at.logic.language.hol.logicSymbols._
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class LKskcTest extends SpecificationWithJUnit {

  "Transformation from LK to LKskc" should {
    val x = HOLVar("x", i)
    val y = HOLVar("y", i)
    val c = HOLConst(new ConstantStringSymbol("c"), i)

    "work for a small proof with only weak quantifiers" in {
      val Rcc = Atom("R", c::c::Nil)
      val Rcx = Atom("R", c::x::Nil)
      val Ryx = Atom("R", y::x::Nil)
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
      val a = HOLVar("a", i)
      val b = HOLVar("b", i)
      val Rab = Atom( "R", a::b::Nil )
      val exyRay = ExVar( y, Atom( "R", a::y::Nil ) )
      val allxexyRxy = AllVar( x, ExVar( y, Atom( "R", x::y::Nil ) ) )
      val ax = LKAxiom( Rab::Nil, Rab::Nil  )
      val r1 = ExistsRightRule( ax, Rab, exyRay, b )
      val r2 = ExistsLeftRule( r1, Rab, exyRay, b )
      val r3 = ForallLeftRule( r2, exyRay, allxexyRxy, a )
      val r4 = ForallRightRule( r3, exyRay, allxexyRxy, a )
      val lkskc_proof = LKtoLKskc( r4, Set() )
      lkskc_proof.root.antecedent.toList.head must beLike{
        case o : LabelledFormulaOccurrence =>
          o.skolem_label == EmptyLabel() && o.formula == r4.root.antecedent.head.formula must_== true
      }
    } 
  }
}
