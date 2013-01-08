/*
 * SkolemizationTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.skolemization

import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.calculi.lk.lkSpecs.{beSyntacticMultisetEqual, beMultisetEqual}

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
import at.logic.calculi.lk.propositionalRules.{AndRightRule, Axiom}
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lksk.base.TypeSynonyms._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.skolemSymbols.SkolemSymbolFactory
import skolemize._
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
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
      skolemize( f, 1, stream ) must beEqualTo( f )
    }

    "introduce correctly a Skolem constant" in {
      val skfun = HOLConst( stream.head, i )
      val skf = Atom( "P", skfun::Nil )
      skolemize( f, 0, stream ) must beEqualTo( skf )
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
      skolemize( f2, 1, stream ) must beEqualTo( skf )

      // now we skolemize the skolemize formula, with opposite polarity
      val skfun2 = HOLConst( stream.tail.tail.head, i )
      val skfun3 = Function( stream.tail.head, skfun2::Nil, i )
      val skf3 = Atom( "R", skfun2::skfun3::Nil )
      val skf4 = Imp( skf1, skf3 )
      skolemize( skolemize( f2, 1, stream ), 0, stream.tail ) must beEqualTo( skf4 )
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
      res.root.toFSequent must beEqualTo (proof_sk.root.toFSequent)
    }

    "work for a cut-free proof (1)" in {
      /* Proof is:
                 R(a,b) :- R(a,b)
                 ----------------------   Ex,r
                 R(a,b) :- ex y. R(a,y)
            ---------------------------   Ex,l
            ex y.R(a,y) :- ex y. R(a,y)
      ---------------------------------- All,l
      all x.ex y.R(x,y) :- ex y. R(a,y)
      --------------------------------------- All,r
      all x.ex y.R(x,y) :- all x.ex y. R(x,y)

      Skolemized: (wrote s0 instead of s_{0} for easier reading)
          R(s1,s0(s1)) :- R(s1,s0(s1))
          ----------------------------   Ex,r
          R(s1,s0(s1)) :- ex y. R(s1,y)
      ---------------------------------- All,l
      all x.R(x,s0(x)) :- ex y. R(s1,y)
       */

      val a = HOLVar("a", i)
      val b = HOLVar("b", i)
      val Rab = Atom( "R", a::b::Nil )
      val exyRay = ExVar( y, Atom( "R", a::y::Nil ) )
      val allxexyRxy = AllVar( x, ExVar( y, Atom( "R", x::y::Nil ) ) )
      val ax = Axiom( Rab::Nil, Rab::Nil )
      val r1 = ExistsRightRule( ax, ax.root.succedent(0), exyRay, b )
      val r2 = ExistsLeftRule( r1, r1.root.antecedent(0) , exyRay, b )
      val r3 = ForallLeftRule( r2, r2.root.antecedent(0), allxexyRxy, a )
      val proof : LKProof = ForallRightRule( r3, exyRay, allxexyRxy, a )

      val fs0 = HOLConst( new ConstantStringSymbol("s_{0}"), i -> i )
      val s1c = HOLConst( new ConstantStringSymbol("s_{2}"), i)
      val s0s1 = HOLApp( fs0,  s1c)
      val sR = Atom( "R", List(s1c,s0s1) )
      val sax = Axiom( List(sR), List(sR) )

      val exyRs1y = ExVar( y, Atom( "R", List(s1c, y )))
//      val exyRs1s0s1 = ExVar( y, Atom( "R", List(a,y) ) )
      val sr1 = ExistsRightRule( sax, sax.root.succedent(0), exyRs1y, s0s1 )

      val allxRxs0x = AllVar( x, Atom( "R", List(x, HOLApp(fs0, x)) ))
      val sr2 = ForallLeftRule( sr1, sr1.root.antecedent(0) , allxRxs0x, s1c )
      val proof_sk = sr2

      SkolemSymbolFactory.reset

      println("=== starting skolemization ===")
      val skolemized_proof : LKProof = skolemize( proof )
      println("=== endsequent skolemized ===")
      println(skolemized_proof.root)
      println(proof_sk.root)

      skolemized_proof.root must beSyntacticMultisetEqual (proof_sk.root)
  }



  }}
