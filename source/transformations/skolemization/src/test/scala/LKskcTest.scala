/*
 * LKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.skolemization.lksk

import org.specs._
import org.specs.runner._

import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.Definitions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.quantifiers._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols._
import at.logic.calculi.lksk.base._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.symbols.ImplicitConverters._
import scala.collection.immutable._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules.{OrLeftRule, Axiom => LKAxiom}
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lksk.base.TypeSynonyms._
import at.logic.language.hol.logicSymbols._

class LKskcTest extends SpecificationWithJUnit {
  "Transformation from LK to LKskc" should {
    "work for a small proof" in {
      val c = HOLConst(new ConstantStringSymbol("c"), i)
      val x = HOLVar("x", i)
      val y = HOLVar("y", i)
      val Rcc = Atom("R", c::c::Nil)
      val Rcx = Atom("R", c::x::Nil)
      val Ryx = Atom("R", y::x::Nil)
      val allxRcx = AllVar( x, Rcx )
      val allyallxRyx = AllVar( y, AllVar( x, Ryx ) )
      val proof = ForallLeftRule( 
                    ForallLeftRule( 
                      LKAxiom( Sequent( Rcc::Nil, Nil ) )._1,
                    Rcc, allxRcx, c ),
                  allxRcx, allyallxRyx, c )
      val lkskc_proof = LKtoLKskc( proof )
      lkskc_proof.root.antecedent.toList.first must beLike {case o : LabelledFormulaOccurrence => o.label == EmptyLabel() && o.formula == proof.root.antecedent.toList.first.formula }
    }
  }
}
