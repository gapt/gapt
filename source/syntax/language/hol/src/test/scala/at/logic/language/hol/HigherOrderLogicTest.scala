/*
 * HigherOrderLogicTest.scala
 */

package at.logic.language.hol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.types._
import at.logic.language.lambda._
import at.logic.language.lambda.symbols._
import logicSymbols._
import skolemSymbols._
import at.logic.language.hol.BetaReduction._

@RunWith(classOf[JUnitRunner])
class HigherOrderLogicTest extends SpecificationWithJUnit {

  "HigherOrderLogic" should {
    val c1 = HOLConst("a", Ti->To)
    val v1 = HOLVar("x", Ti)
    val a1 = HOLApp(c1, v1)
    val c2 = HOLVar("a", Ti->(Ti->To))
    val v21 = HOLVar("x", Ti)
    val v22 = HOLVar("y", Ti)
    val a21 = HOLApp(c2, v21)
    val a22 = HOLApp(a21, v22)

    "mix correctly the formula trait (1)" in {
      val result = a1 match {
        case x: HOLFormula => true
        case _ => false
      }
      result must beTrue
    }
    "mix correctly the formula trait (2)" in {
      val result = a22 match {
        case x: HOLFormula => true
        case _ => false
      }
      result must beTrue
    }
    "mix correctly the formula trait (3)" in {
      val at1 = Atom(HOLVar("P", ->(c2.exptype, ->(a22.exptype, To))), c2::a22::Nil)
      // Another way to construct P's type is: FunctionType(To, args.map(a => a.exptype) )
      val result = at1 match {
        case x: HOLFormula => true
        case _ => false
      }
      result must beTrue
    }
    "And connective should return the right And formula" in {
      val c1 = Atom(HOLConst("a", To))
      val c2 = Atom(HOLConst("b", To))
      val result = And(c1, c2) match {
        case HOLApp(HOLApp(andC, c1), c2) => true
        case _ => false
      }
      result must beTrue
      }
    "Or connective should return the right formula" in {
      val c1 = Atom(HOLConst("a", To))
      val c2 = Atom(HOLConst("b", To))
      val result = Or(c1, c2) match {
        case HOLApp(HOLApp(orC, c1), c2) => true
        case _ => false
      }
      result must beTrue
    }
    "Imp connective should return the right formula" in {
      val c1 = Atom(HOLVar("a", To))
      val c2 = Atom(HOLVar("b", To))
      val result = Imp(c1, c2) match {
        case HOLApp(HOLApp(impC, c1), c2) => true
        case _ => false
      }
      result must beTrue
    }
    "Neg connective should " in {
      "return the right formula" in {
        val c1 = Atom(HOLVar("a", To))
        val result = Neg(c1) match {
          case HOLApp(negC, c1) => true
          case _ => false
        }
        result must beTrue
      }
      "be extracted correctly" in {
        val e = HOLApp(HOLConst("g","(i -> i)"), HOLConst("c", "i")::Nil)
        val result = e match {
          case Neg(_) => false
          case _ => true
        }
        result must beTrue
      }
    }

    "substitute and normalize correctly when Substitution is applied" in {
      val x = HOLVar("X", Ti -> To )
      val f = HOLVar("f", (Ti -> To) -> Ti )
      val xfx = HOLApp(x, HOLApp( f, x ) )

      val z = HOLVar("z", Ti)
      val p = HOLVar("P", Ti -> To)
      val Pz = HOLApp( p, z )
      val t = HOLAbs( z, Pz )
      val pft = HOLApp( p, HOLApp( f, t ))

      val sigma = Substitution( x, t )

      betaNormalize( sigma( xfx ) ) must beEqualTo( pft )
    }

    "substitute and normalize correctly when Substitution is applied on the formula level" in {
      val x = HOLVar("X", Ti -> To )
      val f = HOLVar("f", (Ti -> To) -> Ti )
      val xfx = Atom(x, Function( f, x::Nil )::Nil )

      val z = HOLVar("z", Ti)
      val p = HOLVar("P", Ti -> To)
      val Pz = HOLApp( p, z )
      val t = HOLAbs( z, Pz )
      val pft = Atom( p, Function( f, t::Nil )::Nil )

      val sigma = Substitution( x, t )
      val xfx_sigma = betaNormalize( sigma( xfx ) )

      xfx_sigma must beEqualTo( pft )
    }
  }

  "Exists quantifier" should {
    val c1 = HOLConst("a", Ti->To)
    val v1 = HOLVar("x", Ti)
    val f1 = Atom(c1,v1::Nil)
    "create a term of the right type" in {
      (ExVar(v1, f1).exptype) must beEqualTo (To)
    }
  }

  "Forall quantifier" should {
    val c1 = HOLConst("a", Ti->To)
    val v1 = HOLVar("x", Ti)
    val f1 = Atom(c1,v1::Nil)
    "create a term of the right type" in {
      (AllVar(v1, f1).exptype) must beEqualTo (To)
    }
  }

  "Atoms" should {
    "be extracted correctly" in {
      val p = HOLConst("P", To)
      val result = p match {
        case Atom(HOLConst("P", To), Nil) => true
        case _ => false
      }
      result must beTrue
    }
  }
  
  "Equation" should {
    "be of the right type" in {
      val c1 = HOLConst("f1", Ti -> Ti)
      val c2 = HOLConst("f2", Ti -> Ti)
      val eq = Equation(c1,c2)
      val HOLApp(HOLApp(t,_), _) = eq
      t.exptype must beEqualTo ((Ti -> Ti) -> ((Ti -> Ti) -> To))
    }
  }

  "Substitution" should {
    "work correctly on some testcase involving free/bound vars" in {
      val s0 = HOLConst("s_{0}", Ti -> Ti)
      val C = HOLConst("C", Ti -> Ti)
      val T = HOLConst("T", Ti -> Ti)
      val sCTn = Function(s0, Function( C, Function( T, HOLConst("n", Ti)::Nil)::Nil)::Nil )
      val u = HOLVar("u", Ti)
      val v = HOLVar("v", Ti)
      val P1 = Atom( HOLVar("P", ->(sCTn.exptype, ->(Ti, To))), sCTn::u::Nil)
      val P2 = Atom( HOLVar("P", ->(sCTn.exptype, ->(Ti, To))), sCTn::v::Nil)
      val q_form = AllVar(u, ExVar(v, Imp(P1, P2)))
      
      q_form match {
        case AllVar(x, f) => {
          val a = HOLConst("a", x.exptype)
          val sub = Substitution( x, a )
          val P3 = Atom(HOLVar("P", ->(sCTn.exptype, ->(a.exptype, To))), sCTn::a::Nil)
          val s = sub( f )
          val result = s match {
            case ExVar(v, Imp(P3, P2)) => true
            case _ => false
          }
          result must beTrue
        }
      }
    }
  }

  "SkolemSymbolFactory" should {
      val x = HOLVar("x", Ti)
      val y = HOLVar("y", Ti)
      val f = AllVar( x, Atom(HOLVar("P", ->(Ti, To)), x::Nil ) )
      val s0 = new StringSymbol( "s_{0}" )
      val s1 = new StringSymbol( "s_{2}" )
      val s2 = new StringSymbol( "s_{4}" )
      val s3 = new StringSymbol( "s_{6}" )

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
      val f = And(Atom(HOLVar("P", To),Nil), Atom(HOLVar("P", To),Nil))

      f must beLike {
        case Atom(_,_) => println("Is an atom"); ko
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

  "Quantifier blocks" should {
    val x = HOLVar("x", Ti)
    val y = HOLVar("y", Ti)
    val z = HOLVar("z", Ti)

    val Pxyz = Atom(HOLConst("P", ->(Ti,->(Ti,(->(Ti,To))))), List(x,y,z))
    val allP = AllVar(x, AllVar(y, AllVar(z, Pxyz)))
    val exP = ExVar(x, ExVar(y, ExVar(z, Pxyz)))

    "Correctly introduce one quantifier" in {
      AllVarBlock(List(x), Pxyz) must beEqualTo(AllVar(x, Pxyz))
      ExVarBlock(List(x), Pxyz) must beEqualTo(ExVar(x, Pxyz))
    }

    "Correctly introduce multiple quantifiers" in {
      AllVarBlock(List(x,y,z), Pxyz) must beEqualTo(allP)
      ExVarBlock(List(x,y,z), Pxyz) must beEqualTo(exP)
    }

    "Correctly match quantified formulas" in {

      val match1 = allP match {
        case AllVarBlock(vars, f) =>
          vars == List(x,y,z)
          f == Pxyz
        case _ => false
      }

      val match2 = exP match {
        case ExVarBlock(vars, f) =>
          vars == List(x,y,z)
          f == Pxyz
        case _ => false
      }

      match1 must beTrue
      match2 must beTrue
    }

    "Fail to match other formulas" in {
      exP match {
        case AllVarBlock(_,_) => failure
        case _ =>
      }

      allP match {
        case ExVarBlock(_,_) => failure
        case _ =>
      }

      Pxyz match {
        case AllVarBlock(_,_) | ExVarBlock(_,_) => failure
        case _ =>
      }

      success
    }
  }
}
