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
import LogicSymbols._
import LogicSymbols.LogicSymbolsImplicitConverters._
import Symbols.SymbolImplicitConverters._
import Types.TAImplicitConverters._
import HigherOrderLogic._

class HigherOrderLogicTest extends Specification with JUnit {
  "HigherOrderLogic" should {
      "use the right implicit AppFactory" in {
          val c1: HOL = HOLConst("a", i->o)
          val v1: HOL = HOLVar("x", i)
          val a1 = App[HOL](c1,v1)
          (a1) must beLike {case x: HOLFormula => true}
          val c2: HOL = HOLConst("a", i->(i->o))
          val v21: HOL = HOLVar("x", i)
          val v22: HOL = HOLVar("y", i)
          val a21 = App[HOL](c2,v21)
          val a22 = App[HOL](a21.asInstanceOf[HOL],v22)
          (a22) must beLike {case x: HOLFormula => true}
      }
      "And connective should return the right And formula" in {
          val c1: HOLFormula = HOLConst("a", o).asInstanceOf[HOLFormula]
          val c2: HOLFormula = HOLConst("b", o).asInstanceOf[HOLFormula]
          (c1 and c2) must beLike {case App(App(andC, c1), c2) => true}
      }
    /*"create atoms correctly" in {
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
    }*/

  }
}