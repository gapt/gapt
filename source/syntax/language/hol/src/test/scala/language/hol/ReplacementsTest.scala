/*
 * ReplacementsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.hol

import org.specs._
import org.specs.runner._

import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
import logicSymbols._
import logicSymbols.ImplicitConverters._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import ImplicitConverters._
import Definitions._
import replacements._

class ReplacementsTest extends SpecificationWithJUnit {
  "Replacements" should {
    "work correctly on" in {
      "Atoms" in {
        val a = HOLConst(new ConstantStringSymbol("a"), i)
        val b = HOLConst(new ConstantStringSymbol("b"), i)
        val atom1 = Atom("P", a::Nil)
        val atom2 = Atom("P", b::Nil)
        val pos = List(1)
        val rep = Replacement(pos, b)
        (rep.apply(atom1)) must beEqual (atom2)
      }
    }
  }
}
