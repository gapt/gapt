/*
 * LogicExpressionsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.hol

import org.specs._
import org.specs.runner._

import at.logic.language.lambda.Types._
import at.logic.language.lambda.TypedLambdaCalculus._
import at.logic.language.lambda.Symbols._
import LogicSymbols._
import LogicSymbols.LogicSymbolsDefaultConverters._
//import at.logic.language.lambda.Symbols.SymbolImplicitConverters._
import at.logic.language.lambda.Types.TAImplicitConverters._
import HigherOrderLogic._

class HigherOrderLogicTest extends Specification with JUnit {
    "HigherOrderLogic" should {
        val c1 = HOLConst(new ConstantStringSymbol("a"), i->o)
        val v1 = Var("x", i, hol)
        val a1 = App(c1,v1)
        val c2 = Var("a", i->(i->o), hol)
        val v21 = Var("x", i, hol)
        val v22 = Var("y", i, hol)
        val a21 = App(c2,v21)
        val a22 = App(a21,v22)
    "mix correctly the formula trait (1)" in {
          
          (a1) must beLike {case x: Formula => true}
    }
    "mix correctly the formula trait (2)" in {
          
          (a22) must beLike {case x: Formula => true}
    }
    "mix correctly the formula trait (3)" in {
          val at1 = Atom("P", c2::a22::Nil)
          (at1) must beLike {case x: Formula => true}
    }
    "And connective should return the right And formula" in {
          val c1 = HOLConstFormula(new ConstantStringSymbol("a"))
          val c2 = HOLConstFormula(new ConstantStringSymbol("b"))
          (c1 and c2) must beLike {case App(App(andC, c1), c2) => true}
      }
    "Or connective should return the right formula" in {
          val c1 = HOLConstFormula(new ConstantStringSymbol("a"))
          val c2 = HOLConstFormula(new ConstantStringSymbol("b"))
          (c1 or c2) must beLike {case App(App(orC, c1), c2) => true}
      }
    "Imp connective should return the right formula" in {
          val c1 = Var("a", o, hol).asInstanceOf[Formula]
          val c2 = Var("b", o, hol).asInstanceOf[Formula]
          (c1 imp c2) must beLike {case App(App(impC, c1), c2) => true}
    }
    "Neg connective should return the right formula" in {
          val c1 = Var("a", o, hol).asInstanceOf[Formula]
          (Neg(c1)) must beLike {case App(negC, c1) => true}
    }
    "Constants are created correctly using the default implicit converter" in {
        val c1 = Var("a", i->o, hol)
        val v1 = Var("x", i, hol)
        (c1) must beLike {case x: Const => true}
        (v1) must beLike {
            case x: Const => false
            case _ => true
        }
    }
  }
}
