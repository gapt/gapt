/*
 * LambdaCalculusTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambdatry

import org.specs._
import org.specs.runner._


import at.logic.language.lambda.Types._
import at.logic.language.lambda.Symbols._
import at.logic.language.lambda.Symbols.SymbolImplicitConverters._
import TypedLambdaCalculus._

class LambdaCalculusTryTest extends Specification with JUnit {
  "LambdaCalculusTry" should {
    "create higher-order atom formulas" in {
      ExpressionFactory.factory = HOLFactory
      val f = new Var( "f", i -> o )
      val g = new Var( "g", (i -> o) -> o )
      // P(f, g)
      val a = Atom( "P", f::g::Nil )
      (a) must beLike{ case x: HOLFormula => true }
    }
  }
}
