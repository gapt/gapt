/*
 * SubstitutionsTest.scala
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
import substitutions._
import types.Definitions._
import substitutions.ImplicitConverters._

class SubstitutionsTest extends SpecificationWithJUnit {
  level = Info  // sets the printing of extra information (level can be: Debug, Info, Warning, Error)
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
      println("\n\n\n"+sub.toString+"\n\n\n")
      sub must beEqual (sub2)
    }

    "make implicit conversion from pair to Substitution" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val e = App(f, x)
      val sigma: Substitution[LambdaExpression] = (v,e)
      val eta = (v,e)
      ( Substitution(eta) ) must beEqual ( sigma )
    }
    "make implicit conversion from Substitution to pair" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val e = App(f, x)
      val eta = (v,e)
      val sigma = Substitution(eta)
      ( sigma: Tuple2[Var, LambdaExpression] ) must beEqual ( eta )
    }
    "substitute correctly when Substitution is applied (1)" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val e = App(f, x)
      val d = (v,e)
      val sigma: Substitution[LambdaExpression] = Substitution(d)
      ( e ) must beEqual ( sigma(v) )
    }
    "substitute correctly when Substitution is applied (2)" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val e = App(f, x)
      val d = (v,e)
      val sigma: Substitution[LambdaExpression] = d
      val expression = App(f, v)
      ( App(f, App(f, x)) ) must beEqual ( sigma(expression) )
    }
    "substitute correctly when Substitution is applied (3)" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val y = LambdaVar("y", i)
      val e = App(f, x)
      val sigma: Substitution[LambdaExpression] = (v,e)
      val expression = Abs(y, App(f, v))
      ( Abs(y,App(f, App(f, x))) ) must beEqual ( sigma(expression) )
    }
    /*"substitute correctly when Substitution is applied (4)" in {
      "(λx1:i.x2((λx3:i.v(x1:i):o)):o)"
      val x1 = LambdaVar("x1", i); val x2 = LambdaVar("x2", i->o); val x3 = LambdaVar("x3", i); val v = LambdaVar("v", )
      val y = LambdaVar("y", i)
      val e = App(f, x)
      val sigma: Substitution = (v,e)
      val expression = Abs(y, App(f, v))
      ( Abs(y,App(f, App(f, x))) ) must beEqual ( sigma(expression) )
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
                ( isDifferent ) must beEqual ( true )
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
                ( isDifferent ) must beEqual ( true )
            }*/
    "concatenate/compose 2 Substitutions correctly" in {
      val v = LambdaVar("v", i); val x = LambdaVar("x", i); val f = LambdaVar("f", i -> i)
      val e = App(f, x)
      val sigma: Substitution[LambdaExpression] = (v,e)
      val sigma1 = sigma::(Substitution())
      val sigma2 = sigma::sigma::(Substitution())
      val sigma3 = sigma1:::sigma1
      ( sigma2 ) must beEqual ( sigma3 )
    }
    "substitute correctly when Substitution is applied" in {
      val v = LambdaVar("v", i) 
      val x = LambdaVar("x", i)
      val f = LambdaVar("f", i -> i)
      val e = App(f, v)
      val sigma1: Substitution[LambdaExpression] = (v,x)
      ( sigma1(e) ) must beEqual ( App(f,x) )
    }
  }
  "Substitution with regard to de-Bruijn indices" should {
    "not substitute for bound variables in (\\x.fx)x with sub {x |-> gy}" in {
      val term1 = App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("x",i))
      val sub: Substitution[LambdaExpression] = (LambdaVar("x",i), App(LambdaVar("g",i->i),LambdaVar("y",i)))
      val term2 = App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),App(LambdaVar("g",i->i),LambdaVar("y",i)))
      (sub(term1)) must beEqual (term2)
    }
    "not substitute for bound variables in (\\x.fx)x with sub {x |-> (\\x.fx)c}" in {
      "- 1" in {
        val term1 = App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("x",i))
        val sub: Substitution[LambdaExpression] = (LambdaVar("x",i), App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("c",i)))
        val term2 = App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("c",i)))
        (sub(term1)) must beEqual (term2)
      }
      "- 2" in {
        val term1 = App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("x",i))
        val sub: Substitution[LambdaExpression] = (LambdaVar("x",i), App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("c",i)))
        val term2 = App(Abs(LambdaVar("z",i), App(LambdaVar("f",i->i),LambdaVar("z",i))),App(Abs(LambdaVar("w",i), App(LambdaVar("f",i->i),LambdaVar("w",i))),LambdaVar("c",i)))
        (sub(term1)) must beEqual (term2)
      }
    }
    "recompute correctly indices when substituting a term with bound variables into the scope of other bound variables" in {
      val term1 = Abs(LambdaVar("x",i), App(LambdaVar("F",i->i),LambdaVar("x",i)))
      val sub: Substitution[LambdaExpression] = (LambdaVar("F",i->i), Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))))
      val term2 = Abs(LambdaVar("x",i), App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("x",i)))
      (sub(term1)) must beEqual (term2)
    }
  }
  "work correctly on subterms of abs (i.e. the variables which were bound there are no longer bound)" in {
    val term1 = Abs(LambdaVar("F",i->i),Abs(LambdaVar("x",i), App(LambdaVar("F",i->i),LambdaVar("x",i))))
    val sub: Substitution[LambdaExpression] = (term1.variable, Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))))
    val term2 = Abs(LambdaVar("x",i), App(Abs(LambdaVar("x",i), App(LambdaVar("f",i->i),LambdaVar("x",i))),LambdaVar("x",i)))
    (sub(term1.expression)) must beEqual (term2)
  }
}
