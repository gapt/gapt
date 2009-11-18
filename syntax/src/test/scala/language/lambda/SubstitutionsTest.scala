/*
 * SubstitutionsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import org.specs._
import org.specs.runner._


import Types._
import Symbols._
import Symbols.SymbolImplicitConverters._
import TypedLambdaCalculus._
import Substitutions._


class SubstitutionsTest extends Specification with JUnit {
  level = Info  // sets the printing of extra information (level can be: Debug, Info, Warning, Error)
  "Substitutions" should {
    "make implicit conversion from pair to SingleSubstitution" in {
        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
        val e = App(f, x)
        val sigma = SingleSubstitution[Lambda](v,e)
        val eta = (v,e)
        ( eta : SingleSubstitution[Lambda] ) must beEqual ( sigma )
    }
    "make implicit conversion from SingleSubstitution to pair" in {
        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
        val e = App(f, x)
        val sigma = SingleSubstitution[Lambda](v,e)
        val eta = (v,e)
        ( eta ) must beEqual ( sigma : Tuple2[Var[Lambda],LambdaExpression[Lambda]] )
    }
    "substitute correctly when SingleSubstitution is applied (1)" in {
        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
        val e = App(f, x)
        val d = (v,e)
        val sigma: SingleSubstitution[Lambda] = d
        ( e ) must beEqual ( sigma(v) )
    }
    "substitute correctly when SingleSubstitution is applied (2)" in {
        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
        val e = App(f, x)
        val d = (v,e)
        val sigma: SingleSubstitution[Lambda] = d
        val expression = App(f, v)
        ( App(f, App(f, x)) ) must beEqual ( sigma(expression) )
    }
//    "substitute correctly when SingleSubstitution is applied (3)" in {
//        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
//        val y = Var[Lambda]("y", i)
//        val e = App(f, x)
//        val sigma: SingleSubstitution[Lambda] = (v,e)
//        val expression = Abs(y, App(f, v))
//        ( Abs(y,App(f, App(f, x))) ) must beEqual ( sigma(expression) )
//    }
//    "substitute correctly when SingleSubstitution is applied, renaming bound variables (1)" in {
//        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
//        val e = App(f, x)
//        val sigma: SingleSubstitution[Lambda] = (v,e)
//        val exp1 = Abs(x, App(f, v))
//        val exp2 = sigma(exp1)
//        debug(exp2.toString)
//        val exp3 = Abs(x,App(f, App(f, x)))
//        val isDifferent = !(exp2==exp3)
//        ( isDifferent ) must beEqual ( true )
//    }
//    "substitute correctly when SingleSubstitution is applied, renaming bound variables (2)" in {
//        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
//        val e = App(f, x)
//        val sigma: SingleSubstitution[Lambda] = (v,e)
//        val exp1 = Abs(f, App(f, v))
//        val exp2 = sigma(exp1)
//        debug(exp2.toString)
//        val exp3 = Abs(f,App(f, App(f, x)))
//        val isDifferent = !(exp2==exp3)
//        ( isDifferent ) must beEqual ( true )
//    }
//    "create Substitution correctly" in {
//        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
//        val e = App(f, x)
//        val sigma: SingleSubstitution[Lambda] = (v,e)
//        val sigma1 = Substitution[Lambda]( sigma::Nil )
//        val sigma2 = Substitution[Lambda]( List(sigma) )
//        val sigma3 = new Substitution[Lambda](v,e)  // Unfortunately, we need the keyword "new" when we use alternative constructors of the case class...
//        val sigma4 = new Substitution[Lambda](sigma)  // Unfortunately, we need the keyword "new" when we use alternative constructors of the case class...
//        val sigma5:Substitution[Lambda] = (v,e)
//        val sigma6:Substitution[Lambda] = sigma
//        val areEqual = ((sigma1==sigma2) && (sigma2==sigma3) && (sigma3==sigma4) && (sigma4==sigma5) && (sigma5==sigma6))
//        ( areEqual ) must beEqual ( true )
//    }
//    "substitute correctly when Substitution is applied" in {
//        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
//        val e = App(f, x)
//        val sigma: SingleSubstitution[Lambda] = (v,e)
//        val sigma1 = Substitution[Lambda]( sigma::Nil )
//        val exp = App(f, v)
//        ( sigma(exp) ) must beEqual ( sigma1(exp) )
//    }
//    "cons SingleSubstitution with Substitution correctly" in {
//        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
//        val e = App(f, x)
//        val sigma: SingleSubstitution[Lambda] = (v,e)
//        val sigma1 = Substitution[Lambda]( sigma::Nil )
//        val sigma2 = Substitution[Lambda]( sigma::sigma::Nil )
//        val sigma3 = sigma::sigma1
//        val sigma4 = sigma1:::sigma1
//        ( sigma2 ) must beEqual ( sigma3 )
//    }
//    "concatenate/compose 2 Substitutions correctly" in {
//        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val f = Var[Lambda]("f", i -> i)
//        val e = App(f, x)
//        val sigma: SingleSubstitution[Lambda] = (v,e)
//        val sigma1 = Substitution[Lambda]( sigma::Nil )
//        val sigma2 = Substitution[Lambda]( sigma::sigma::Nil )
//        val sigma3 = sigma1:::sigma1
//        ( sigma2 ) must beEqual ( sigma3 )
//    }
//    "substitute correctly when Substitution is applied" in {
//        val v = Var[Lambda]("v", i); val x = Var[Lambda]("x", i); val y = Var[Lambda]("y", i);
//        val f = Var[Lambda]("f", i -> i)
//        val e = App(f, v)
//        val sigma1: SingleSubstitution[Lambda] = (v,x)
//        val sigma2: SingleSubstitution[Lambda] = (x,y)
//        val sigma3 = Substitution[Lambda]( sigma1::sigma2::Nil )
//        ( sigma3(e) ) must beEqual ( App(f,y) )
//    }
  }
}
