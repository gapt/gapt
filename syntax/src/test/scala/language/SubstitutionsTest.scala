/*
 * SubstitutionsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import org.specs._
import org.specs.runner._


import Types._
import Symbols._
import Symbols.StringSymbolImplicitConverters._
import TypedLambdaCalculus._
import Substitutions._



class SubstitutionsTest extends Specification with JUnit {
  "Substitutions" should {
    "make implicit conversion from pair to SingleSubstitution" in {
        val v = Var("v", i)
        val x = Var("x", i)
        val f = Var("v", i -> i)
        val e = App(f, x)
        val sigma = SingleSubstitution(v,e)
        val eta = (v,e)
        ( eta : SingleSubstitution ) must beEqual ( sigma )
    }
    "make implicit conversion from SingleSubstitution to pair" in {
        val v = Var("v", i)
        val x = Var("x", i)
        val f = Var("v", i -> i)
        val e = App(f, x)
        val sigma = SingleSubstitution(v,e)
        val eta = (v,e)
        ( eta ) must beEqual ( sigma : Tuple2[Var,LambdaExpression] )
    }
    "make implicit conversion from SingleSubstitution to pair" in {
        val v = Var("v", i)
        val x = Var("x", i)
        val f = Var("v", i -> i)
        val e = App(f, x)
        val sigma: SingleSubstitution = (v,e)
        ( e ) must beEqual ( sigma(v) )
    }
  }
}
