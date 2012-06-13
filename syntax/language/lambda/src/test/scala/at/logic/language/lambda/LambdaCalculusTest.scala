/*
 * LambdaCalculusTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import types._
import symbols._
import symbols.ImplicitConverters._
import typedLambdaCalculus._
import types.Definitions._
import scala.math.signum

@RunWith(classOf[JUnitRunner])
class LambdaCalculusTest extends SpecificationWithJUnit {
  private case class MyVar(nm: String) extends Var(VariableStringSymbol(nm), Ti())
  "TypedLambdaCalculus" should {
    "make implicit conversion from String to Name" in {
      (LambdaVar("p",i) ) must beEqualTo (LambdaVar("p", i ))
    }
    "export lambda expressions to strings correctly (1)" in {
      val exp = LambdaVar("P", i)
      (exportLambdaExpressionToString(exp)) must beEqualTo ("P")
    }
    "export lambda expressions to strings correctly (2)" in {
      val exp = App(LambdaVar("P", i -> o), LambdaVar("x",i))
      (exportLambdaExpressionToString(exp)) must beEqualTo ("(P x)")
    }
    "export lambda expressions to strings correctly (3)" in {
      val exp1 = LambdaVar("x",i)
      val exp2 = App(LambdaVar("P", i -> o), exp1)
      val exp3 = Abs(exp1,exp2)
      (exportLambdaExpressionToString(exp3)) must beEqualTo ("\\x.(P x)")
    }
    "create N-ary abstractions (AbsN) correctly" in {
      val v1 = LambdaVar("x",i)
      val v2 = LambdaVar("y",i)
      val f = LambdaVar("f",i -> (i -> o))
      ( AbsN(v1::v2::Nil, f) match {
        case Abs(v1,Abs(v2,f)) => true
        case _ => false
        }) must beEqualTo ( true )
    }
    "create N-ary applications (AppN) correctly" in {
      val v1 = LambdaVar("x",i)
      val v2 = LambdaVar("y",i)
      val f = LambdaVar("f",i -> (i -> o))
      ( AppN(f, List(v1,v2)) match {
        case App(App(f, v1), v2) => true
        case _ => false
        }) must beEqualTo ( true )
    }
  }

  "AbsN1" should {
    "extract correctly" in {
      (LambdaVar("x",i)) must not (beLike {case AbsN1(_,_) => ok})
    }
  }
  
  "De Bruijn Indices" should {
    "work correctly for alpha conversion" in {
      val a1 = Abs(MyVar("y"), App(LambdaVar("x",i->i), MyVar("y")))
      val b1 = Abs(MyVar("z"), App(LambdaVar("x",i->i), MyVar("z")))
      "- (\\y.xy) = (\\z.xz)" in {
        (a1) must beEqualTo (b1)
      }
      val a2 = Abs(MyVar("y"), a1)
      val b2 = Abs(MyVar("w"), a1)
      "- (\\y.\\y.xy) = (\\w.\\y.xy)" in {
        (a2) must beEqualTo (b2)
      }
      val a3 = Abs(MyVar("y"), App(Abs(MyVar("y"), MyVar("x")), MyVar("y")))
      val b3 = Abs(MyVar("w"), App(Abs(MyVar("y"), MyVar("x")), MyVar("w")))
      "- (\\y.(\\y.x)y) = (\\w.(\\y.x)w)" in {
        (a3) must beEqualTo (b3)
      }
      val a4 = Abs(MyVar("y"), App(Abs(MyVar("y"), MyVar("x")), MyVar("y")))
      val b4 = Abs(MyVar("y"), App(Abs(MyVar("y"), MyVar("x")), MyVar("w")))
      "- (\\y.(\\y.x)y) != (\\y.(\\y.x)w)" in {
        (a4) must not be equalTo (b4)
      }
      val a5 = Abs(MyVar("y"), App(Abs(MyVar("y"), MyVar("y")), MyVar("y")))
      val b5 = Abs(MyVar("y"), App(Abs(MyVar("w"), MyVar("w")), MyVar("y")))
      "- (\\y.(\\y.y)y) = (\\y.(\\w.w)y)" in {
        (a5) must beEqualTo (b5)
      }
      val a6 = Abs(MyVar("y"), App(Abs(MyVar("y"), MyVar("y")), MyVar("y")))
      val b6 = Abs(MyVar("y"), App(Abs(MyVar("w"), MyVar("y")), MyVar("x")))
      "- (\\y.(\\y.y)y) != (\\y.(\\w.y)y)" in {
        (a6) must not be equalTo (b6)
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
      free must not (have(_ =^ x ))
      free must have (_ =^ y )
      free must have (_ =^ z )
      free must have (_ =^ r )
      bound must have (_ =^ x)
      bound must not (have (_ =^ y))
      bound must not (have (_ =^ z))
      bound must not (have (_ =^ r))
  }
  

  "correctly order expressions" in {
    val x = LambdaVar(VariableStringSymbol("x"), i )
    val y = LambdaVar(VariableStringSymbol("y"), i )

    val xx = Abs( x, x )
    val yy = Abs( y, y )
    val xy = Abs( x, y )

    xx.compare( yy ) must beEqualTo( 0 )
    xx.compare( xy ) must not be equalTo( 0 )
    yy.compare( xy ) must not be equalTo( 0 )
    xy.compare( xx ) must not be equalTo( 0 )
    xy.compare( yy ) must not be equalTo( 0 )
    signum( xx.compare( xy ) ) * signum( xy.compare( xx ) ) must beEqualTo ( -1 )

    val f = LambdaVar(VariableStringSymbol("f"), i -> i)
    val g = LambdaVar(VariableStringSymbol("g"), i -> i)
    val fx = App( f, x )
    val gx = App( g, x )
    val fy = App( f, y )

    fx.compare( gx ) must beEqualTo( -1 )
    gx.compare( fx ) must beEqualTo( 1 )
    fx.compare( fy ) must beEqualTo( -1 )
    fy.compare( fx ) must beEqualTo( 1 )

    fx.compare( xx ) must not be equalTo ( 0 )
    fx.compare( xx ) * xx.compare( fx ) must beEqualTo ( -1 )
    fx.compare( yy ) * yy.compare( fx ) must beEqualTo ( -1 )

    val xfx = Abs( x, fx )
    val yfx = Abs( y, fx )
    val yfy = Abs( y, fy )

    xfx.compare( yfy ) must beEqualTo( 0 )
    xfx.compare( yfx ) must not be equalTo( 0 )
    xfx.compare( yfx ) * yfx.compare( xfx ) must beEqualTo( -1 )
  }

  "deal correctly with bound variables in the Abs extractor" in {
    val x = LambdaVar(VariableStringSymbol("x"), i)
    val p = LambdaVar(VariableStringSymbol("p"), i -> o)
    val px = App(p, x)
    val xpx = Abs(x, px)

    val res = xpx match {
      case Abs(v, t) => Abs(v, t)
    }

    res must beEqualTo( xpx )
  }
}
