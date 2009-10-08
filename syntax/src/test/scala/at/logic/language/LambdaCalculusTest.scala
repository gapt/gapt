/*
 * LambdaCalculusTest.scala
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


class LambdaCalculusTest extends Specification with JUnit {
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
    "create N-ary abstractions (AbsN) correctly" in {
        val v1 = Var("x",i)
        val v2 = Var("y",i)
        val f = Var("f",i -> (i -> o))
        // ( AbsN(v1::v2::Nil, f) ) must beEqual ( Abs(v1,Abs(v2,f)) )
        ( AbsN(v1::v2::Nil, f) match {
            case Abs(v1,Abs(v2,f)) => true
            case _ => false
            }) must beEqual ( true )
    }

  }
}
