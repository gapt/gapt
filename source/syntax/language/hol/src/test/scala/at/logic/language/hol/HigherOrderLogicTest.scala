/*
 * LogicExpressionsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.hol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
import logicSymbols._
import logicSymbols.ImplicitConverters._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import ImplicitConverters._
import Definitions._
import at.logic.language.lambda.substitutions._
import skolemSymbols._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._

@RunWith(classOf[JUnitRunner])
class HigherOrderLogicTest extends SpecificationWithJUnit {

  "HigherOrderLogic" should {
    val c1 = HOLConst(new ConstantStringSymbol("a"), i->o)
    val v1 = Var("x", i, hol)
    val a1 = App(c1,v1)
    val c2 = Var("a", i->(i->o), HOLFactory)
    val v21 = Var("x", i, HOLFactory)
    val v22 = Var("y", i, HOLFactory)
    val a21 = App(c2,v21)
    val a22 = App(a21,v22)

    "mix correctly the formula trait (1)" in {
      (a1) must beLike {case x: Formula => ok}
    }
    "mix correctly the formula trait (2)" in {
      (a22) must beLike {case x: Formula => ok}
    }
    "mix correctly the formula trait (3)" in {
      val at1 = Atom("P", c2::a22::Nil)
      (at1) must beLike {case x: Formula => ok}
    }
    "And connective should return the right And formula" in {
      val c1 = HOLConstFormula(new ConstantStringSymbol("a"))
      val c2 = HOLConstFormula(new ConstantStringSymbol("b"))
      (c1 and c2) must beLike {case App(App(andC, c1), c2) => ok}
      }
    "Or connective should return the right formula" in {
      val c1 = HOLConstFormula(new ConstantStringSymbol("a"))
      val c2 = HOLConstFormula(new ConstantStringSymbol("b"))
      (c1 or c2) must beLike {case App(App(orC, c1), c2) => ok}
      }
    "Imp connective should return the right formula" in {
      val c1 = Var("a", o, HOLFactory).asInstanceOf[HOLFormula]
      val c2 = Var("b", o, HOLFactory).asInstanceOf[HOLFormula]
      (c1 imp c2) must beLike {case App(App(impC, c1), c2) => ok}
    }
    "Neg connective should " in {
      "return the right formula" in {
        val c1 = Var("a", o, HOLFactory).asInstanceOf[HOLFormula]
        (Neg(c1)) must beLike {case App(negC, c1) => ok}
      }
      "be extracted correctly" in {
        (AppN(HOLConst(new ConstantStringSymbol("g"),"(i -> i)"), HOLConst(new ConstantStringSymbol("c"), "i")::Nil)) must not (beLike {case Neg(c) => ok})
      }
    }
    "Constants are created correctly using the default implicit converter" in {
      val c1 = Var("a", i->o, HOLFactory)
      val v1 = Var("x", i, HOLFactory)
      (c1) must beLike {case x: Const => ok}
      (v1) must beLike {
        case x: Const => ko
        case _ => ok
      }
    }
    "substitute and normalize correctly when Substitution is applied" in {
      val x = HOLVar(VariableStringSymbol("X"), i -> o )
      val f = HOLVar(VariableStringSymbol("f"), (i -> o) -> i )
      val xfx = HOLApp(x, HOLApp( f, x ) )

      val z = HOLVar(VariableStringSymbol("z"), i)
      val p = HOLVar(VariableStringSymbol("P"), i -> o)
      val Pz = HOLApp( p, z )
      val t = HOLAbs( z, Pz )

      val sigma = Substitution[HOLExpression]( x, t )

      betaNormalize( sigma.apply( xfx ) ) must beEqualTo( HOLApp( p, HOLApp( f, t ) ) )
    }
  }

  "Exists quantifier" should {
    val c1 = HOLConst(new ConstantStringSymbol("a"), i->o)
    val v1 = HOLVar(new VariableStringSymbol("x"), i)
    val f1 = HOLAppFormula(c1,v1)
    "create a term of the right type" in {
      (ExVar(v1, f1).exptype) must beEqualTo (o)
    }
  }

  "Forall quantifier" should {
    val c1 = HOLConst(new ConstantStringSymbol("a"), i->o)
    val v1 = HOLVar(new VariableStringSymbol("x"), i)
    val f1 = HOLAppFormula(c1,v1)
    "create a term of the right type" in {
      (AllVar(v1, f1).exptype) must beEqualTo (o)
    }
  }

  "Atoms" should {
    "be extracted correctly" in {
      (HOLConst(new ConstantStringSymbol("P"), o)) must beLike {case Atom(ConstantStringSymbol("P"), Nil) => ok}
    }
  }
  
  "Equation" should {
    "be of the right type" in {
      val c1 = HOLConst(new ConstantStringSymbol("f1"), i -> i)
      val c2 = HOLConst(new ConstantStringSymbol("f2"), i -> i)
      val eq = Equation(c1,c2)
      val App(App(t,_), _) = eq
      t.exptype must beEqualTo ((i -> i) -> ((i -> i) -> o))
    }
  }

  "Complex AppN" should {
    "be extracted correctly" in {
      AppN( HOLConst( new ConstantStringSymbol("\\cap"),"((i -> o) -> ((i -> o) -> (i -> o)))"),
          HOLVar( new VariableStringSymbol("X"), "(i -> o)" )::HOLVar( new VariableStringSymbol("Y"), "(i -> o)" )::Nil) must beLike {
        case AppN(Var(ConstantStringSymbol(_),FunctionType(To(),(->(Ti(),To()))::(->(Ti(),To()))::Ti()::Nil)),args) => ok
      }
    }
  }
  
  "Substitution" should {
    "work correctly on some testcase involving free/bound vars" in {
      val s0 = HOLConst(new ConstantStringSymbol("s_{0}"), i -> i)
      val C = HOLConst(new ConstantStringSymbol("C"), i -> i)
      val T = HOLConst(new ConstantStringSymbol("T"), i -> i)
      val sCTn = Function(s0, Function( C, Function( T, HOLConst(new ConstantStringSymbol("n"), i)::Nil)::Nil)::Nil )
      val u = HOLVar(new VariableStringSymbol("u"), i)
      val v = HOLVar(new VariableStringSymbol("v"), i)
      val P1 = Atom( "P", sCTn::u::Nil)
      val P2 = Atom( "P", sCTn::v::Nil)
      val q_form = AllVar(u, ExVar(v, Imp(P1, P2)))
      q_form match {
        case AllVar(x, f) => {
          val a = HOLConst(new ConstantStringSymbol("a"), x.exptype)
          val sub : Substitution[HOLExpression] = Substitution( x, a )
          val P3 = Atom("P", sCTn::a::Nil)
          sub( f ) must beEqualTo( ExVar(v, Imp(P3, P2)))
        }
      }
    }
  }

  "SkolemSymbolFactory" should {
      val x = HOLVar(new VariableStringSymbol("x"), i)
      val y = HOLVar(new VariableStringSymbol("y"), i)
      val f = AllVar( x, Atom("P", x::Nil ) )
      val s0 = new ConstantStringSymbol( "s_{0}" )
      val s1 = new ConstantStringSymbol( "s_{2}" )
      val s2 = new ConstantStringSymbol( "s_{4}" )
      val s3 = new ConstantStringSymbol( "s_{6}" )

      SkolemSymbolFactory.reset
      val stream = SkolemSymbolFactory.getSkolemSymbols

    "return a correct stream of Skolem symbols" in {
      stream.head must beEqualTo( s0 )
      stream.tail.head must beEqualTo( s1 )
      stream.tail.tail.head must beEqualTo( s2 )
    }
  }

  "Higher Order Formula matching" should {
    "not allow P and P match as an Atom " in {
      val ps = new ConstantStringSymbol("P")
      val f = And(Atom(ps,Nil), Atom(ps,Nil))

      f must beLike {
        case Atom(_,_) => ko
        case Function(_,_,_) => ko
        case AllVar(_,_) => ko
        case ExVar(_,_) => ko
        case Or(_,_) => ko
        case Imp(_,_) => ko
        case And(_,_) => ok
        case _ => ko
      }
    }
  }
}
