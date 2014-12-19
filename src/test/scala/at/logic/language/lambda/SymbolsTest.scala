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
      (VariantSymbol("a")) must beEqualTo (VariantSymbol("a"))
    }
    "return true if they have the same string and number" in {
      (VariantSymbol("a", 0)) must beEqualTo (VariantSymbol("a", 0))
    }
    "return false if the two are of the same class but different strings" in {
      (VariantSymbol("a")) must not be equalTo (VariantSymbol("b"))
    }
    "return false if they have the same string but different numbers" in {
      (VariantSymbol("a", 0)) must not be equalTo (VariantSymbol("a", 1))
    }
  }
}

