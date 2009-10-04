/*
 * typedLambdaCalculusTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import org.specs._
import org.specs.runner._


import Types._
import TypedLambdaCalculus._
import TypedLambdaCalculus.StringSymbolImplicitConverters._


class TypedLambdaCalculusTest extends Specification with JUnit {
  "TypedLambdaCalculus" should {
    "make implicit conversion from String to Name" in {      
        (Var("p",i) ) must beEqual (Var(StringSymbol("p"), i ))
    }
    "export lambda expressions to strings correctly (1)" in {
        val exp = Var("P", i)
        (exportLambdaExpressionToString(exp)) must beEqual ("P")
    }
    "export lambda expressions to strings correctly (2)" in {
        val exp = App(Var("P", i -> o), Var("x",i))
        (exportLambdaExpressionToString(exp)) must beEqual ("(P x)")
    }
    "export lambda expressions to strings correctly (3)" in {
        val exp1 = Var("x",i)
        val exp2 = App(Var("P", i -> o), exp1)
        val exp3 = Abs(exp1,exp2)
        (exportLambdaExpressionToString(exp3)) must beEqual ("\\x.(P x)")
    }
  }
}
