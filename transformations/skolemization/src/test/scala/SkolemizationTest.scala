/*
 * SkolemizationTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.skolemization

import org.specs._
import org.specs.runner._

import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols._
import at.logic.calculi.lksk.base._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.symbols.ImplicitConverters._
import scala.collection.immutable._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules.{OrLeftRule, Axiom => LKAxiom}
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lksk.base.TypeSynonyms._
import at.logic.language.hol.logicSymbols._

class SkolemizationTest extends SpecificationWithJUnit {
  "Skolemization" should {
      val x = HOLVar(new VariableStringSymbol("x"), i)
      val f = AllVar( x, Atom("P", x::Nil ) )

    "have a correct stream of Skolem symbols" in {
      skolemize.skolem_symbol_stream.head must beEqual( new ConstantStringSymbol( "s_0" ) )
      skolemize.skolem_symbol_stream.tail.head must beEqual( new ConstantStringSymbol( "s_1" ) )
      skolemize.skolem_symbol_stream.tail.tail.head must beEqual( new ConstantStringSymbol( "s_2" ) )
    }

    "have a correct even/odd function" in {
      val s_even = skolemize.even(skolemize.skolem_symbol_stream)
      val s_odd = skolemize.odd(skolemize.skolem_symbol_stream)
      s_even.head must beEqual( new ConstantStringSymbol( "s_0" ) )
      s_odd.head must beEqual( new ConstantStringSymbol( "s_1" ) )
      s_even.tail.head must beEqual( new ConstantStringSymbol( "s_2" ) )
      s_odd.tail.head must beEqual( new ConstantStringSymbol( "s_3" ) )
    }   
    
    "leave a formula with only weak quantifiers untouched" in {
      skolemize( f, 1 ) must beEqual( f )
    }

    "introduce correctly a Skolem constant" in {
      val skfun = HOLConst( skolemize.skolem_symbol_stream.head, i )
      val skf = Atom( "P", skfun::Nil )
      skolemize( f, 0 ) must beEqual( skf )
    }

    "handle a binary formula correctly" in {
      val y = HOLVar(new VariableStringSymbol("y"), i)
      val rxy = Atom( "R", x::y::Nil )
      val f2 = Imp(f, AllVar( x, ExVar( y, rxy ) ) )

      val skfun0 = HOLConst( skolemize.skolem_symbol_stream.head, i )
      val skfun1 = Function( skolemize.skolem_symbol_stream.tail.head, x::Nil, i )
      val skf1 = Atom( "P", skfun0::Nil )
      val skf2 = Atom( "R", x::skfun1::Nil )

      val skf = Imp( skf1, AllVar( x, skf2 ) )
      skolemize( f2, 1 ) must beEqual( skf )
    }
  }
}
