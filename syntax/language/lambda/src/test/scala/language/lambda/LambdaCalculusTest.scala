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
  private case class MyVar(nm: String) extends Var(VariableStringSymbol(nm), Ti())
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
  "AbsN1" should {
    "extract correctly" in {
      (LambdaVar("x",i)) mustNot beLike {case AbsN1(_,_) => true}
    }
  }
  "De Bruijn Indices" should {
    "work correctly for alpha conversion" in {
      val a1 = Abs(MyVar("y"), App(LambdaVar("x",i->i), MyVar("y")))
      val b1 = Abs(MyVar("z"), App(LambdaVar("x",i->i), MyVar("z")))
      "- (\\y.xy) = (\\z.xz)" in {
        (a1) must beEqual (b1)
      }
      val a2 = Abs(MyVar("y"), a1)
      val b2 = Abs(MyVar("w"), a1)
      "- (\\y.\\y.xy) = (\\w.\\y.xy)" in {
        (a2) must beEqual (b2)
      }
      val a3 = Abs(MyVar("y"), App(Abs(MyVar("y"), MyVar("x")), MyVar("y")))
      val b3 = Abs(MyVar("w"), App(Abs(MyVar("y"), MyVar("x")), MyVar("w")))
      "- (\\y.(\\y.x)y) = (\\w.(\\y.x)w)" in {
        (a3) must beEqual (b3)
      }
      val a4 = Abs(MyVar("y"), App(Abs(MyVar("y"), MyVar("x")), MyVar("y")))
      val b4 = Abs(MyVar("y"), App(Abs(MyVar("y"), MyVar("x")), MyVar("w")))
      "- (\\y.(\\y.x)y) != (\\y.(\\y.x)w)" in {
        (a4) mustNot beEqual (b4)
      }
      val a5 = Abs(MyVar("y"), App(Abs(MyVar("y"), MyVar("y")), MyVar("y")))
      val b5 = Abs(MyVar("y"), App(Abs(MyVar("w"), MyVar("w")), MyVar("y")))
      "- (\\y.(\\y.y)y) = (\\y.(\\w.w)y)" in {
        (a5) must beEqual (b5)
      }
      val a6 = Abs(MyVar("y"), App(Abs(MyVar("y"), MyVar("y")), MyVar("y")))
      val b6 = Abs(MyVar("y"), App(Abs(MyVar("w"), MyVar("y")), MyVar("x")))
      "- (\\y.(\\y.y)y) != (\\y.(\\w.y)y)" in {
        (a6) mustNot beEqual (b6)
      }
    }
  }

  "extract free and bound variables correctly" in {
      val x = LambdaVar(VariableStringSymbol("X"), i -> o )
      val y = LambdaVar(VariableStringSymbol("y"), i )
      val z = LambdaVar(VariableStringSymbol("Z"), i -> o )
      val r = LambdaVar(VariableStringSymbol("R"), (i -> o) -> (i -> ((i -> o) -> o)))
      val a = AppN(r, x::y::z::Nil)
      val qa = Abs( x, a )
      val free = qa.getFreeAndBoundVariables._1
      val bound = qa.getFreeAndBoundVariables._2
      free must notExist(_ =^ x )
      free must exist(_ =^ y )
      free must exist(_ =^ z )
      free must exist(_ =^ r )
      bound must exist (_ =^ x)
      bound must notExist (_ =^ y)
      bound must notExist (_ =^ z)
      bound must notExist (_ =^ r)
  }
}
