/*
 * SymbolsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import symbols._

@RunWith(classOf[JUnitRunner])
class SymbolsTest extends SpecificationWithJUnit {
  "Equality between symbols" should {
    "return true if it is the same class and mixed with the same string" in {
      (new VariableStringSymbol("a")) must beEqualTo (new VariableStringSymbol("a"))
    }
    "return false if the two are of the same class but different strings" in {
      (new VariableStringSymbol("a")) must not be equalTo (new VariableStringSymbol("b"))
    }
  }
}

