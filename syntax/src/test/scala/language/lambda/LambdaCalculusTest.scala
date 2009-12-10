/*
 * LambdaCalculusTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import org.specs._
import org.specs.runner._

import types._
import symbols._
import symbols.ImplicitConverters._
import typedLambdaCalculus._
import types.Definitions._

class LambdaCalculusTest extends SpecificationWithJUnit {
  "TypedLambdaCalculus" should {
    "make implicit conversion from String to Name" in {
      (LambdaVar("p",i) ) must beEqual (LambdaVar("p", i ))
    }
    "export lambda expressions to strings correctly (1)" in {
      val exp = LambdaVar("P", i)
      (exportLambdaExpressionToString(exp)) must beEqual ("P")
    }
    "export lambda expressions to strings correctly (2)" in {
      val exp = App(LambdaVar("P", i -> o), LambdaVar("x",i))
      (exportLambdaExpressionToString(exp)) must beEqual ("(P x)")
    }
    "export lambda expressions to strings correctly (3)" in {
      val exp1 = LambdaVar("x",i)
      val exp2 = App(LambdaVar("P", i -> o), exp1)
      val exp3 = Abs(exp1,exp2)
      (exportLambdaExpressionToString(exp3)) must beEqual ("\\x.(P x)")
    }
    "create N-ary abstractions (AbsN) correctly" in {
      val v1 = LambdaVar("x",i)
      val v2 = LambdaVar("y",i)
      val f = LambdaVar("f",i -> (i -> o))
      ( AbsN(v1::v2::Nil, f) match {
        case Abs(v1,Abs(v2,f)) => true
        case _ => false
        }) must beEqual ( true )
    }
    "create N-ary applications (AppN) correctly" in {
      val v1 = LambdaVar("x",i)
      val v2 = LambdaVar("y",i)
      val f = LambdaVar("f",i -> (i -> o))
      ( AppN(f, List(v1,v2)) match {
        case App(App(f, v1), v2) => true
        case _ => false
        }) must beEqual ( true )
    }
  }
  "AbsN" should {
    "extract correctly" in {
      (LambdaVar("x",i)) mustNot beLike {case AbsN(_,_) => true}
    }
  }
}
