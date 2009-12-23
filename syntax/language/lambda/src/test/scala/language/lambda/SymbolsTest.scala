/*
 * SymbolsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import org.specs._
import org.specs.runner._


import symbols._

class SymbolsTest extends SpecificationWithJUnit {
  "Equality between symbols" should {
    "return true if it is the same class" in {
      (new VariableSymbolA {}) must beEqual (new VariableSymbolA {})
    }
    "return true if it is the same class and mixed with the same string" in {
      (new VariableStringSymbol("a")) must beEqual (new VariableStringSymbol("a"))
    }
    "return false if the two are of the same class but different strings" in {
      (new VariableStringSymbol("a")) mustNot beEqual (new VariableStringSymbol("b"))
    }
  }
}

