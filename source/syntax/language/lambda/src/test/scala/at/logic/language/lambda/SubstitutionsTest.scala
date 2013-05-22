/*
 * SubstitutionsTest.scala
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
import substitutions._
import types.Definitions._
import substitutions.ImplicitConverters._
import BetaReduction._
import ImplicitStandardStrategy._
import org.specs2.execute.Success

@RunWith(classOf[JUnitRunner])
class SubstitutionsTest extends SpecificationWithJUnit {

  "Substitutions" should {
    "NOT compose the substitution {f(y)/x} and {g(y)/x}" in {
      val x = LambdaVar("x", i);
      val y = LambdaVar("y", i);
      val f = LambdaVar("f", i -> i)
      val g = LambdaVar("g", i -> i)
      val e1 = App(f, y)
      val e2 = App(g, y)
      val sub1 = Substitution(x,e1)
      val sub2 = Substitution(x,e2)
      val sub = sub1 compose sub2
      //println("\n\n\n"+sub.toString+"\n\n\n")
      sub must beEqualTo (sub2)
    }

    "make implicit conversion from pair to Substitution" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val e = App(f, x)
      val sigma: Substitution[LambdaExpression] = (v,e)
      val eta = (v,e)
      ( Substitution(eta) ) must beEqualTo ( sigma )
    }
    "make implicit conversion from Substitution to pair" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val e = App(f, x)
      val eta = (v,e)
      val sigma = Substitution(eta)
      ( sigma: Tuple2[Var, LambdaExpression] ) must beEqualTo ( eta )
    }
    "substitute correctly when Substitution is applied (1)" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val e = App(f, x)
      val d = (v,e)
      val sigma: Substitution[LambdaExpression] = Substitution(d)
      ( e ) must beEqualTo ( sigma(v) )
    }
    "substitute correctly when Substitution is applied (2)" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val e = App(f, x)
      val d = (v,e)
      val sigma: Substitution[LambdaExpression] = d
      val expression = App(f, v)
      ( App(f, App(f, x)) ) must beEqualTo ( sigma(expression) )
    }
    "substitute correctly when Substitution is applied (3)" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val y = LambdaVar("y", i)
      val e = App(f, x)
      val sigma: Substitution[LambdaExpression] = (v,e)
      val expression = Abs(y, App(f, v))
      ( Abs(y,App(f, App(f, x))) ) must beEqualTo ( sigma(expression) )
    }
    /*"substitute correctly when Substitution is applied (4)" in {
      "(λx1:i.x2((λx3:i.v(x1:i):o)):o)"
      val x1 = LambdaVar("x1", i); val x2 = LambdaVar("x2", i->o); val x3 = LambdaVar("x3", i); val v = LambdaVar("v", )
      val y = LambdaVar("y", i)
      val e = App(f, x)
      val sigma: Substitution = (v,e)
      val expression = Abs(y, App(f, v))
      ( Abs(y,App(f, App(f, x))) ) must beEqualTo ( sigma(expression) )
    }*/
            /*"substitute correctly when SingleSubstitution is applied, renaming bound variables (1)" in {
                val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
                val e = App(f, x)
                val sigma: SingleSubstitution = (v,e)
                val exp1 = Abs(x, App(f, v))
                val exp2 = sigma(exp1)
                debug(exp2.toString)
                val exp3 = Abs(x,App(f, App(f, x)))
                val isDifferent = !(exp2==exp3)
                ( isDifferent ) must beEqualTo ( true )
            }
            "substitute correctly when SingleSubstitution is applied, renaming bound variables (2)" in {
                val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
                val e = App(f, x)
                val sigma: SingleSubstitution = (v,e)
                val exp1 = Abs(f, App(f, v))
                val exp2 = sigma(exp1)
                debug(exp2.toString)
                val exp3 = Abs(f,App(f, App(f, x)))
                val isDifferent = !(exp2==exp3)
                ( isDifferent ) must beEqualTo ( true )
            }*/

    "substitute and normalize correctly when Substitution is applied" in {
      val x = LambdaVar(VariableStringSymbol("X"), i -> o )
      val f = LambdaVar(VariableStringSymbol("f"), (i -> o) -> i )
      val xfx = App(x, App( f, x ) )

      val z = LambdaVar(VariableStringSymbol("z"), i)
      val p = LambdaVar(VariableStringSymbol("P"), i -> o)
      val Pz = App( p, z )
      val t = Abs( z, Pz )

      val sigma = Substitution[LambdaExpression]( x, t )

      betaNormalize( sigma.apply( xfx ) ) must beEqualTo( App( p, App( f, t ) ) )
    }

    "concatenate/compose 2 Substitutions correctly" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val e = App(f, x)
      val sigma: Substitution[LambdaExpression] = (v,e)
//      val sigma1: Substitution[LambdaExpression] = sigma::(Substitution().asInstanceOf[Substitution[LambdaExpression]])
      val sigma1: Substitution[LambdaExpression] = sigma::(Substitution[LambdaExpression]())
      val sigma2 = sigma::sigma::(Substitution[LambdaExpression]())
      val sigma3 = sigma1:::sigma1
      ( sigma2 ) must beEqualTo ( sigma3 )
    }
    "substitute correctly when Substitution is applied" in {
      val v = LambdaVar("v", i) 
      val x = LambdaVar("x", i)
      val f = LambdaVar("f", i -> i)
      val e = App(f, v)
      val sigma1: Substitution[LambdaExpression] = (v,x)
      ( sigma1(e) ) must beEqualTo ( App(f,x) )
    }
  }
  "Substitution with regard to de-Bruijn indices" should {
    "not substitute for bound variables in (\\x.fx)x with sub {x |-> gy}" in {
      val term1 = App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("x",i))
      val sub: Substitution[LambdaExpression] = (LambdaVar("x",i), App(LambdaVar("g",i->i),LambdaVar("y",i)))
      val term2 = App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),App(LambdaVar("g",i->i),LambdaVar("y",i)))
      (sub(term1)) must beEqualTo (term2)
    }
    "not substitute for bound variables in (\\x.fx)x with sub {x |-> (\\x.fx)c}" in {
      "- 1" in {
        val term1 = App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("x",i))
        val sub: Substitution[LambdaExpression] = (LambdaVar("x",i), App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("c",i)))
        val term2 = App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("c",i)))
        (sub(term1)) must beEqualTo (term2)
      }
      "- 2" in {
        val term1 = App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("x",i))
        val sub: Substitution[LambdaExpression] = (LambdaVar("x",i), App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("c",i)))
        val term2 = App(Abs(LambdaVar("z",i), App(LambdaVar("f",i->i),LambdaVar("z",i))),App(Abs(LambdaVar("w",i), App(LambdaVar("f",i->i),LambdaVar("w",i))),LambdaVar("c",i)))
        (sub(term1)) must beEqualTo (term2)
      }
    }
    "recompute correctly indices when substituting a term with bound variables into the scope of other bound variables" in {
      val term1 = Abs(LambdaVar("x",i), App(LambdaVar("F",i->i),LambdaVar("x",i)))
      val sub: Substitution[LambdaExpression] = (LambdaVar("F",i->i), Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))))
      val term2 = Abs(LambdaVar("x",i), App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("x",i)))
      (sub(term1)) must beEqualTo (term2)
    }
    "work correctly on subterms of abs (i.e. the variables which were bound there are no longer bound)" in {
      val term1 = Abs(LambdaVar("F",i->i),Abs(LambdaVar("x",i), App(LambdaVar("F",i->i),LambdaVar("x",i))))
      val sub: Substitution[LambdaExpression] = (term1.variable, Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))))
      val term2 = Abs(LambdaVar("x",i), App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("x",i)))
      (sub(term1.expression)) must beEqualTo (term2)
    }
  }

  "Normalization of Lambdaterms" should {
    val x = LambdaVar(new VariableStringSymbol("x"), Ti())
    val y = LambdaVar(new VariableStringSymbol("y"), Ti())
    val P = LambdaVar(new VariableStringSymbol("P"), (Ti() -> Ti()) -> ((Ti() -> Ti()) -> To()))
    val v1 = LambdaVar(new VariableStringSymbol("v_{1}"), Ti())
    val v2 = LambdaVar(new VariableStringSymbol("v_{2}"), Ti())
    val v3 = LambdaVar(new VariableStringSymbol("v_{3}"), Ti())
    val t1 = AppN(P, List(Abs(x,x), Abs(x,x)))
    val t2 = AppN(P, List(Abs(y,y), Abs(x,x)))
    val t3 = AppN(P, List(Abs(x,y), Abs(y,x)))
    val t4 = AppN(P, List(Abs(y,x), Abs(x,x)))

    val tn1 = AppN(P, List(Abs(v1,v1), Abs(v2,v2)))
    val tn2 = tn1
    val tn3 = AppN(P, List(Abs(x,y), Abs(y,x)))
    val tn4 = AppN(P, List(Abs(y,x), Abs(x,x)))


    "work for variables of same name but bound to different binders" in {
      val n3 = Normalization(t3, 0, "v")._1
      println(n3)
      val n4 = Normalization(t4, 0, "v")._1
      println(n4)
      val n1 = Normalization(t1, 0, "v")._1
      n1 must beEqualTo(tn1)
      val n2 = Normalization(t2, 0, "v")._1
      n2 must beEqualTo(tn2)
    }
  }

}
