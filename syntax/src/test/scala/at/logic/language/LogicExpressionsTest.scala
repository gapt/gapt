/*
 * LogicExpressionsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import org.specs._
import org.specs.runner._

import Types._
import TypedLambdaCalculus._
import Symbols._
import Symbols.StringSymbolImplicitConverters._
import LogicExpressions._

class LogicExpressionsTest extends Specification with JUnit {
  "LogicExpressions" should {
    "create atoms correctly" in {
        val v1 = Var("x",i)
        val v2 = Var("y",i)
        val p = Var("P",i -> (i -> o))
        val a1 = Atom(p, List(v1,v2))
        val a2 = App(App(p, v1), v2)
        ( a1 ) must beEqual ( a2 )
    }
    "pattern match atoms correctly (1)" in {
        val v1 = Var("x",i)
        val v2 = Var("y",i)
        val p = Var("P",i -> (i -> o))
        ( App(App(p, v1), v2) match {
            case Atom(p, List(v1,v2)) => true
            case _ => false
            }) must beEqual ( true )
    }
    "pattern match atoms correctly (2)" in {
        val v1 = Var("x",i)
        val v2 = Var("y",i)
        val p = Var("P",i -> (i -> o))
        ( (Atom(p, List(v1,v2)):LambdaExpression) match {
            case App(App(p, v1), v2) => true
            case _ => false
            }) must beEqual ( true )
    }

  }
}