/*
 * ResolutionTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.resolution

import at.logic.calculi.resolution.robinson.{Resolution, Paramodulation, InitialClause}
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.lambda.substitutions._
import at.logic.calculi.occurrences._
import at.logic.language.hol._
import at.logic.language.fol.{FOLExpression, FOLVar, FOLConst, FOLFormula, Function => FOLFunction, Atom => FOLAtom, Equation => FOLEquation}
import at.logic.language.hol.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.ImplicitConverters._
import base._
import at.logic.calculi.lk.base._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import collection.immutable.Map.Map1
import at.logic.calculi.lk.lkSpecs._

//import robinson._
//import andrews._
import at.logic.language.hol.Definitions._
import at.logic.language.hol.skolemSymbols.SkolemSymbolFactory

@RunWith(classOf[JUnitRunner])
class ResolutionTest extends SpecificationWithJUnit {
/*
  val pa = Atom(ConstantStringSymbol("p"),Var(ConstantStringSymbol("a"), i, hol)::Nil)
  val pfx = Atom(ConstantStringSymbol("p"),Function(ConstantStringSymbol("f"), Var(VariableStringSymbol("x"), i, hol)::Nil,i)::Nil)
  val px = Atom(ConstantStringSymbol("p"),Var(VariableStringSymbol("x"), i, hol)::Nil)
  val pffa = Atom(ConstantStringSymbol("p"),Function(ConstantStringSymbol("f"),Function(ConstantStringSymbol("f"), Var(ConstantStringSymbol("a"), i, hol)::Nil,i)::Nil, i)::Nil)
  val ax1 = InitialSequent(Clause(Nil,pa::Nil))
  val ax2 = InitialSequent(Clause(px::Nil,pfx::Nil))
  val ax3 = InitialSequent(Clause(pffa::Nil,Nil))
  
  "VariantRule" should {
    "create correct Variant proofs" in {
      val pxeq = Atom(ConstantStringSymbol("p"),Var(VariableStringSymbol("v_{1}"), i, hol)::Nil)
      val pfxeq = Atom(ConstantStringSymbol("p"),Function(ConstantStringSymbol("f"), Var(VariableStringSymbol("v_{1}"), i, hol)::Nil,i)::Nil)
      val var1 = Variant(ax2)
      (var1.root.negative.head) must beEqualTo (pxeq)
      (var1.root.positive.head) must beEqualTo (pfxeq)
    }
  }
*/
  "Paramodulation rule in Robinson Resolution" should {
    "be created correctly" in {
      val cl1 = InitialClause(Nil, FOLAtom(ConstantStringSymbol("="), FOLFunction(ConstantStringSymbol("+"), FOLVar(VariableStringSymbol("x"))::FOLVar(VariableStringSymbol("x"))::Nil)::FOLVar(VariableStringSymbol("x"))::Nil)::Nil)
      val cl2 = InitialClause(Nil, FOLAtom(ConstantStringSymbol("="), FOLFunction(ConstantStringSymbol("+"), FOLVar(VariableStringSymbol("y"))::FOLVar(VariableStringSymbol("y"))::Nil)::FOLVar(VariableStringSymbol("y"))::Nil)::Nil)
      val param = Paramodulation(cl1, cl2, cl1.root.succedent(0), cl2.root.succedent(0), FOLAtom(ConstantStringSymbol("="), FOLVar(VariableStringSymbol("y"))::FOLVar(VariableStringSymbol("x"))::Nil), Substitution[FOLExpression]((FOLVar(VariableStringSymbol("x")), FOLVar(VariableStringSymbol("y")))))
      val sq =  Seq(FOLAtom(ConstantStringSymbol("="), FOLVar(VariableStringSymbol("y"))::FOLVar(VariableStringSymbol("y"))::Nil))
      param.root.positive.map(_.formula) must beEqualTo (sq)
      
      //val p =param.toTreeProof
      //println(p)
      //p must beEqual (p)
    }

    "correctly keep the context of demodulated formulas " in {
      val P = ConstantStringSymbol("P")
      val x = VariableStringSymbol("x")
      val List(a,b,c,d,e,f) = List("a","b","c","d","e","f") map (x => FOLConst(ConstantStringSymbol(x)))
      val List(e1,e2,e3,p,q) = List(FOLEquation(a,b), FOLEquation(c,d), FOLEquation(e,f), FOLAtom(P,a::Nil), FOLAtom(P,b::Nil)  )
      val p1 = InitialClause(Nil, List(e1, e2 ))
      val p2 = InitialClause(Nil, List(e3, p))
      val p3 = Paramodulation(p1,p2, p1.root.succedent(0), p2.root.succedent(1), q, Substitution[FOLExpression]())
      val expected_root = FSequent(Nil, List(e2,e3,q))
      println(p3.root)
      println(expected_root)

      p3.root.toFSequent must beSyntacticFSequentEqual(expected_root)
    }
  }
  "extrator on Resolution rule" should {
    "work properly" in {
      val x = FOLVar(VariableStringSymbol("x"))
      val fa = FOLFunction(ConstantStringSymbol("f"), List(FOLConst(ConstantStringSymbol("a"))))
      val Pfa = FOLAtom(ConstantStringSymbol("P"),List(fa))
      val Px = FOLAtom(ConstantStringSymbol("P"),List(x))
      val cl1 = InitialClause(List(), List(Px))
      val cl2 = InitialClause(List(Pfa), List())
      val res = Resolution(cl1, cl2, cl1.root.succedent(0), cl2.root.antecedent(0), Substitution(new Map1(x,fa).asInstanceOf[Map[Var,FOLExpression]]))
      res must beLike { case Resolution(_,_,_,_,_,_) => ok }
    }
  }


 /* "Andrews Resolution" should {
    implicit val factory = PointerFOFactoryInstance

    "refute 'not (A or not A)'" in {
      val a = Atom(ConstantStringSymbol("p"), Nil)
      val s = Sequent(Nil, Neg(Or(a, Neg(a)))::Nil)
      val p0 = InitialSequent[SequentOccurrence](s)
      val p1 = NotT( p0, p0.root.succedent.head )
      val p2 = OrFL( p1, p1.root.antecedent.head )
      val p3 = OrFR( p1, p1.root.antecedent.head )
      val p4 = NotF( p3, p3.root.antecedent.head )
      val p5 = Cut( p4, p2, p4.root.succedent.head, p2.root.antecedent.head )
      p5.root.getSequent must beEqualTo(Sequent(Nil, Nil))
    }

    "handle strong quantifiers correctly" in {
      val x = HOLVar(VariableStringSymbol("X"), i -> o )
      val y = HOLVar(VariableStringSymbol("y"), i )
      val z = HOLVar(VariableStringSymbol("Z"), i -> o )
      val a = Atom(ConstantStringSymbol("R"), x::y::z::Nil)
      val qa = AllVar( x, a )

      qa.getFreeAndBoundVariables._1 must not contain( x )

      val sk = SkolemSymbolFactory.getSkolemSymbol

      // We do not care about the order of arguments. Do we?
      val skt1 = Function( sk, y::z::Nil, i -> o)
      val skt2 = Function( sk, z::y::Nil, i -> o)
      val ska1 = Atom(ConstantStringSymbol("R"), skt1::y::z::Nil )
      val ska2 = Atom(ConstantStringSymbol("R"), skt2::y::z::Nil )

      val p0 = InitialSequent[SequentOccurrence]( Sequent( qa::Nil, Nil ) )
      val p1 = ForallF( p0, p0.root.antecedent.head, sk )

      ska1::ska2::Nil must contain( p1.root.getSequent.antecedent.head )
    }

    "handle weak quantifiers and substitution correctly" in {
      val x = HOLVar(VariableStringSymbol("X"), i -> o )
      val f = HOLConst(ConstantStringSymbol("f"), (i -> o) -> i )
      val xfx = HOLApp(x, HOLApp( f, x ) ).asInstanceOf[HOLFormula]
      val m = AllVar( x, xfx )

      val z = HOLVar(VariableStringSymbol("z"), i)
      val Pz = Atom( ConstantStringSymbol("P"), z::Nil )
      val form = Or(Pz, Neg(Pz))
      val t = HOLAbs( z, form )

      val p0 = InitialSequent[SequentOccurrence]( Sequent( Nil, m::Nil ) )
      val p1 = ForallT( p0, p0.root.succedent.head, x )
      val p2 = Sub( p1, Substitution( x, t ) )

      val newa = Atom( ConstantStringSymbol("P"), HOLApp( f, t )::Nil )
      p2.root.getSequent.succedent.head must beEqualTo( 
        Or( newa, Neg( newa ) ) )
    }
  }      */
}
