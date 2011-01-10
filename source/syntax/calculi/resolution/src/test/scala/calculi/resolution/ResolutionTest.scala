/*
 * ResolutionTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.resolution

import _root_.at.logic.calculi.resolution.robinson.{Paramodulation, InitialClause}
import org.specs._
import org.specs.runner._

import at.logic.language.lambda.substitutions._
import at.logic.calculi.occurrences._
import at.logic.language.hol._
import at.logic.language.fol.{FOLExpression, FOLVar, FOLConst, FOLFormula, Function => FOLFunction, Atom => FOLAtom}
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
//import robinson._
import andrews._
import at.logic.language.hol.Definitions._
import at.logic.language.hol.skolemSymbols.SkolemSymbolFactory

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
      (var1.root.negative.head) must beEqual (pxeq)
      (var1.root.positive.head) must beEqual (pfxeq)
    }
  }
*/
  "Paramodulation rule in Robinson Resolution" should {
    "be created correctly" in {
      import positions._
      val cl1 = InitialClause(Sequent(Nil, FOLAtom(ConstantStringSymbol("="), FOLFunction(ConstantStringSymbol("+"), FOLVar(VariableStringSymbol("x"))::FOLVar(VariableStringSymbol("x"))::Nil)::FOLVar(VariableStringSymbol("x"))::Nil)::Nil))(PositionsFOFactory)
      val cl2 = InitialClause(Sequent(Nil, FOLAtom(ConstantStringSymbol("="), FOLFunction(ConstantStringSymbol("+"), FOLVar(VariableStringSymbol("y"))::FOLVar(VariableStringSymbol("y"))::Nil)::FOLVar(VariableStringSymbol("y"))::Nil)::Nil))(PositionsFOFactory)
      val param = Paramodulation(cl1, cl2, cl1.root.succedent.find(_ == 1).get, cl2.root.succedent.find(_ == 1).get, FOLAtom(ConstantStringSymbol("="), FOLVar(VariableStringSymbol("y"))::FOLVar(VariableStringSymbol("x"))::Nil), Substitution[FOLExpression]((FOLVar(VariableStringSymbol("x")), FOLVar(VariableStringSymbol("y")))))
      val sq = Sequent(Nil, FOLAtom(ConstantStringSymbol("="), FOLVar(VariableStringSymbol("y"))::FOLVar(VariableStringSymbol("y"))::Nil)::Nil)
      param.root.getSequent must beEqual (sq)
    }
  }
  "Andrews Resolution" should {
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
      p5.root.getSequent must beEqual(Sequent(Nil, Nil))
    }

    "handle strong quantifiers correctly" in {
      val x = HOLVar(VariableStringSymbol("X"), i -> o )
      val y = HOLVar(VariableStringSymbol("y"), i )
      val z = HOLVar(VariableStringSymbol("Z"), i -> o )
      val a = Atom(ConstantStringSymbol("R"), x::y::z::Nil)
      val qa = AllVar( x, a )

      qa.getFreeAndBoundVariables._1 must notContain( x )

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
      p2.root.getSequent.succedent.head must beEqual( 
        Or( newa, Neg( newa ) ) )
    }
  }
}
