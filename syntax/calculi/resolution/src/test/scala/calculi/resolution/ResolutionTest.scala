/*
 * ResolutionTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.resolution

import org.specs._
import org.specs.runner._

import at.logic.language.hol._
import at.logic.language.hol.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.ImplicitConverters._
import base._
import at.logic.language.hol.Definitions._

class ResolutionTest extends SpecificationWithJUnit {
  val pa = Atom(ConstantStringSymbol("p"),Var(ConstantStringSymbol("a"), i, hol)::Nil)
  val pfx = Atom(ConstantStringSymbol("p"),Function(ConstantStringSymbol("f"), Var(VariableStringSymbol("x"), i, hol)::Nil,i)::Nil)
  val px = Atom(ConstantStringSymbol("p"),Var(VariableStringSymbol("x"), i, hol)::Nil)
  val pffa = Atom(ConstantStringSymbol("p"),Function(ConstantStringSymbol("f"),Function(ConstantStringSymbol("f"), Var(ConstantStringSymbol("a"), i, hol)::Nil,i)::Nil, i)::Nil)
  val ax1 = Axiom(Clause(Nil,pa::Nil))
  val ax2 = Axiom(Clause(px::Nil,pfx::Nil))
  val ax3 = Axiom(Clause(pffa::Nil,Nil))
  
  "VariantRule" should {
    "create correct Variant proofs" in {
      val pxeq = Atom(ConstantStringSymbol("p"),Var(VariableStringSymbol("v_{1}"), i, hol)::Nil)
      val pfxeq = Atom(ConstantStringSymbol("p"),Function(ConstantStringSymbol("f"), Var(VariableStringSymbol("v_{1}"), i, hol)::Nil,i)::Nil)
      val var1 = Variant(ax2)
      (var1.root.negative.head) must beEqual (pxeq)
      (var1.root.positive.head) must beEqual (pfxeq)
    }
  }
}
