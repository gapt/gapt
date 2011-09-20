/*
 * SkolemizationTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.skolemization

import org.specs._
import org.specs.runner._
import at.logic.calculi.lk.lkSpecs.beMultisetEqual

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
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules.{AndRightRule, Axiom}
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lksk.base.TypeSynonyms._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.skolemSymbols.SkolemSymbolFactory
import skolemize._

class SkolemizationTest extends SpecificationWithJUnit {


  "Skolemization" should {
      val x = HOLVar("x", i)
      val y = HOLVar("y", i)
      val f = AllVar( x, Atom("P", x::Nil ) )
      val s0 = new ConstantStringSymbol( "s_{0}" )
      val s1 = new ConstantStringSymbol( "s_{2}" )
      val s2 = new ConstantStringSymbol( "s_{4}" )
      val s3 = new ConstantStringSymbol( "s_{6}" )
      SkolemSymbolFactory.reset
      val stream = SkolemSymbolFactory.getSkolemSymbols

    "leave a formula with only weak quantifiers untouched" in {
      skolemize( f, 1, stream ) must beEqual( f )
    }

    "introduce correctly a Skolem constant" in {
      val skfun = HOLConst( stream.head, i )
      val skf = Atom( "P", skfun::Nil )
      skolemize( f, 0, stream ) must beEqual( skf )
    }

    "handle a binary formula correctly" in {
      val y = HOLVar(new VariableStringSymbol("y"), i)
      val rxy = Atom( "R", x::y::Nil )
      val f2 = Imp(f, AllVar( x, ExVar( y, rxy ) ) )

      val skfun0 = HOLConst( stream.head, i )
      val skfun1 = Function( stream.tail.head, x::Nil, i )
      val skf1 = Atom( "P", skfun0::Nil )
      val skf2 = Atom( "R", x::skfun1::Nil )

      val skf = Imp( skf1, AllVar( x, skf2 ) )
      skolemize( f2, 1, stream ) must beEqual( skf )

      // now we skolemize the skolemize formula, with opposite polarity
      val skfun2 = HOLConst( stream.tail.tail.head, i )
      val skfun3 = Function( stream.tail.head, skfun2::Nil, i )
      val skf3 = Atom( "R", skfun2::skfun3::Nil )
      val skf4 = Imp( skf1, skf3 )
      skolemize( skolemize( f2, 1, stream ), 0, stream.tail ) must beEqual( skf4 )
    }

    "handle a simple proof correctly" in {
      val s5 = new ConstantStringSymbol( "s_{5}" )
      val cs5 = HOLConst( s5, i )
      val alpha = HOLVar( new VariableStringSymbol( "α" ), i )
      val Palpha = Atom( "P", alpha::Nil )
      val Ps0 = Atom( "P", cs5::Nil )
      val allxPx = AllVar( x, Atom( "P", x::Nil ) )
      val ax = Axiom( Palpha::Nil, Palpha::Nil  )
      val proof = ForallRightRule(
                    ForallLeftRule( ax,
                                    Palpha, allxPx, alpha ),
                    Palpha, allxPx, alpha )

      val ax_sk = Axiom(  Ps0::Nil, Ps0::Nil  )
      val proof_sk = ForallLeftRule( ax_sk, Ps0, allxPx, cs5 )

      val res = skolemize( proof )
      res.root.toFSequent must beEqual (proof_sk.root.toFSequent)
    }

    /*"work for a cut-free proof" in {
      val a = HOLVar("a", i)
      val b = HOLVar("b", i)
      val Rab = Atom( "R", a::b::Nil )
      val exyRay = ExVar( y, Atom( "R", a::y::Nil ) )
      val allxexyRxy = AllVar( x, ExVar( y, Atom( "R", x::y::Nil ) ) )
      val ax = Axiom( Sequent( Rab::Nil, Rab::Nil ) )
      val r1 = ExistsRightRule( ax._1, Rab, exyRay, b )
      val r2 = ExistsLeftRule( r1, Rab, exyRay, b )
      val r3 = ForallLeftRule( r2, exyRay, allxexyRxy, a )
      val proof = ForallRightRule( r3, exyRay, allxexyRxy, a )

      val fs0 = HOLConst( s0, i -> i )
      val cs1 = HOLConst( s1, i )
      val s0s1 = HOLApp( fs0, cs1 )
      val sR = Atom( "R", cs1::s0s1::Nil )
      val sax = Axiom( Sequent( sR::Nil, sR::Nil ) )
      val exyRs1y = ExVar( y, Atom( "R", cs1::y::Nil ) )
      val allxRxs0x = AllVar( x, Atom( "R", x::HOLApp( fs0, x )::Nil ) )

      val sr1 = ExistsRightRule( sax._1, sR, exyRs1y, s0s1 )
      val proof_sk = ForallLeftRule( sr1, sR, allxRxs0x, cs1 )

      // this does not work correctly
      //skolemize( proof ) must beEqual( proof_sk )
      skolemize( proof ).root.getSequent.multisetEquals( proof_sk.root.getSequent) must beEqual( true )    }         */
  }
}
