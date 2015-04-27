/*
 * HigherOrderLogicTest.scala
 */

package at.logic.gapt.language.hol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.gapt.expr.types._
import at.logic.gapt.expr._
import at.logic.gapt.expr.symbols._
import at.logic.gapt.language.hol.BetaReduction._

@RunWith( classOf[JUnitRunner] )
class HigherOrderLogicTest extends SpecificationWithJUnit {

  "HigherOrderLogic" should {
    val c1 = HOLConst( "a", Ti -> To )
    val v1 = HOLVar( "x", Ti )
    val a1 = HOLApp( c1, v1 )
    val c2 = HOLVar( "a", Ti -> ( Ti -> To ) )
    val v21 = HOLVar( "x", Ti )
    val v22 = HOLVar( "y", Ti )
    val a21 = HOLApp( c2, v21 )
    val a22 = HOLApp( a21, v22 )

    "mix correctly the formula trait (1)" in {
      val result = a1 match {
        case x: HOLFormula => true
        case _             => false
      }
      result must beTrue
    }
    "mix correctly the formula trait (2)" in {
      val result = a22 match {
        case x: HOLFormula => true
        case _             => false
      }
      result must beTrue
    }
    "mix correctly the formula trait (3)" in {
      val at1 = HOLAtom( HOLVar( "P", ->( c2.exptype, ->( a22.exptype, To ) ) ), c2 :: a22 :: Nil )
      // Another way to construct P's type is: FunctionType(To, args.map(a => a.exptype) )
      val result = at1 match {
        case x: HOLFormula => true
        case _             => false
      }
      result must beTrue
    }
    "And connective should return the right And formula" in {
      val c1 = HOLAtom( HOLConst( "a", To ) )
      val c2 = HOLAtom( HOLConst( "b", To ) )
      val result = HOLAnd( c1, c2 ) match {
        case HOLApp( HOLApp( andC, c1 ), c2 ) => true
        case _                                => false
      }
      result must beTrue
    }
    "Or connective should return the right formula" in {
      val c1 = HOLAtom( HOLConst( "a", To ) )
      val c2 = HOLAtom( HOLConst( "b", To ) )
      val result = HOLOr( c1, c2 ) match {
        case HOLApp( HOLApp( orC, c1 ), c2 ) => true
        case _                               => false
      }
      result must beTrue
    }
    "Imp connective should return the right formula" in {
      val c1 = HOLAtom( HOLVar( "a", To ) )
      val c2 = HOLAtom( HOLVar( "b", To ) )
      val result = HOLImp( c1, c2 ) match {
        case HOLApp( HOLApp( impC, c1 ), c2 ) => true
        case _                                => false
      }
      result must beTrue
    }
    "Neg connective should " in {
      "return the right formula" in {
        val c1 = HOLAtom( HOLVar( "a", To ) )
        val result = HOLNeg( c1 ) match {
          case HOLApp( negC, c1 ) => true
          case _                  => false
        }
        result must beTrue
      }
      "be extracted correctly" in {
        val e = HOLApp( HOLConst( "g", "(i -> i)" ), HOLConst( "c", "i" ) :: Nil )
        val result = e match {
          case HOLNeg( _ ) => false
          case _           => true
        }
        result must beTrue
      }
    }

    "substitute and normalize correctly when Substitution is applied" in {
      val x = HOLVar( "X", Ti -> To )
      val f = HOLVar( "f", ( Ti -> To ) -> Ti )
      val xfx = HOLApp( x, HOLApp( f, x ) )

      val z = HOLVar( "z", Ti )
      val p = HOLVar( "P", Ti -> To )
      val Pz = HOLApp( p, z )
      val t = HOLAbs( z, Pz )
      val pft = HOLApp( p, HOLApp( f, t ) )

      val sigma = HOLSubstitution( x, t )

      betaNormalize( sigma( xfx ) ) must beEqualTo( pft )
    }

    "substitute and normalize correctly when Substitution is applied on the formula level" in {
      val x = HOLVar( "X", Ti -> To )
      val f = HOLVar( "f", ( Ti -> To ) -> Ti )
      val xfx = HOLAtom( x, HOLFunction( f, x :: Nil ) :: Nil )

      val z = HOLVar( "z", Ti )
      val p = HOLVar( "P", Ti -> To )
      val Pz = HOLApp( p, z )
      val t = HOLAbs( z, Pz )
      val pft = HOLAtom( p, HOLFunction( f, t :: Nil ) :: Nil )

      val sigma = HOLSubstitution( x, t )
      val xfx_sigma = betaNormalize( sigma( xfx ) )

      xfx_sigma must beEqualTo( pft )
    }
  }

  "Exists quantifier" should {
    val c1 = HOLConst( "a", Ti -> To )
    val v1 = HOLVar( "x", Ti )
    val f1 = HOLAtom( c1, v1 :: Nil )
    "create a term of the right type" in {
      ( HOLExVar( v1, f1 ).exptype ) must beEqualTo( To )
    }
  }

  "Forall quantifier" should {
    val c1 = HOLConst( "a", Ti -> To )
    val v1 = HOLVar( "x", Ti )
    val f1 = HOLAtom( c1, v1 :: Nil )
    "create a term of the right type" in {
      ( HOLAllVar( v1, f1 ).exptype ) must beEqualTo( To )
    }
  }

  "Atoms" should {
    "be extracted correctly" in {
      val p = HOLConst( "P", To )
      val result = p match {
        case HOLAtom( HOLConst( "P", To ), Nil ) => true
        case _                                   => false
      }
      result must beTrue
    }
  }

  "Equation" should {
    "be of the right type" in {
      val c1 = HOLConst( "f1", Ti -> Ti )
      val c2 = HOLConst( "f2", Ti -> Ti )
      val eq = HOLEquation( c1, c2 )
      val HOLApp( HOLApp( t, _ ), _ ) = eq
      t.exptype must beEqualTo( ( Ti -> Ti ) -> ( ( Ti -> Ti ) -> To ) )
    }
  }

  "Substitution" should {
    "work correctly on some testcase involving free/bound vars" in {
      val s0 = HOLConst( "s_{0}", Ti -> Ti )
      val C = HOLConst( "C", Ti -> Ti )
      val T = HOLConst( "T", Ti -> Ti )
      val sCTn = HOLFunction( s0, HOLFunction( C, HOLFunction( T, HOLConst( "n", Ti ) :: Nil ) :: Nil ) :: Nil )
      val u = HOLVar( "u", Ti )
      val v = HOLVar( "v", Ti )
      val P1 = HOLAtom( HOLVar( "P", ->( sCTn.exptype, ->( Ti, To ) ) ), sCTn :: u :: Nil )
      val P2 = HOLAtom( HOLVar( "P", ->( sCTn.exptype, ->( Ti, To ) ) ), sCTn :: v :: Nil )
      val q_form = HOLAllVar( u, HOLExVar( v, HOLImp( P1, P2 ) ) )

      q_form match {
        case HOLAllVar( x, f ) => {
          val a = HOLConst( "a", x.exptype )
          val sub = HOLSubstitution( x, a )
          val P3 = HOLAtom( HOLVar( "P", ->( sCTn.exptype, ->( a.exptype, To ) ) ), sCTn :: a :: Nil )
          val s = sub( f )
          val result = s match {
            case HOLExVar( v, HOLImp( P3, P2 ) ) => true
            case _                               => false
          }
          result must beTrue
        }
      }
    }
  }

  "SkolemSymbolFactory" should {
    val x = HOLVar( "x", Ti )
    val y = HOLVar( "y", Ti )
    val f = HOLAllVar( x, HOLAtom( HOLVar( "P", ->( Ti, To ) ), x :: Nil ) )
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
      val f = HOLAnd( HOLAtom( HOLVar( "P", To ), Nil ), HOLAtom( HOLVar( "P", To ), Nil ) )

      f must beLike {
        case HOLAtom( _, _ ) =>
          println( "Is an atom" ); ko
        case HOLFunction( _, _, _ ) => ko
        case HOLAllVar( _, _ )      => ko
        case HOLExVar( _, _ )       => ko
        case HOLOr( _, _ )          => ko
        case HOLImp( _, _ )         => ko
        case HOLAnd( _, _ )         => ok
        case _                      => ko
      }
    }
  }

  "Quantifier blocks" should {
    val x = HOLVar( "x", Ti )
    val y = HOLVar( "y", Ti )
    val z = HOLVar( "z", Ti )

    val Pxyz = HOLAtom( HOLConst( "P", ->( Ti, ->( Ti, ( ->( Ti, To ) ) ) ) ), List( x, y, z ) )
    val allP = HOLAllVar( x, HOLAllVar( y, HOLAllVar( z, Pxyz ) ) )
    val exP = HOLExVar( x, HOLExVar( y, HOLExVar( z, Pxyz ) ) )

    "Correctly introduce one quantifier" in {
      HOLAllVarBlock( List( x ), Pxyz ) must beEqualTo( HOLAllVar( x, Pxyz ) )
      HOLExVarBlock( List( x ), Pxyz ) must beEqualTo( HOLExVar( x, Pxyz ) )
    }

    "Correctly introduce multiple quantifiers" in {
      HOLAllVarBlock( List( x, y, z ), Pxyz ) must beEqualTo( allP )
      HOLExVarBlock( List( x, y, z ), Pxyz ) must beEqualTo( exP )
    }

    "Correctly match quantified formulas" in {

      val match1 = allP match {
        case HOLAllVarBlock( vars, f ) =>
          vars == List( x, y, z )
          f == Pxyz
        case _ => false
      }

      val match2 = exP match {
        case HOLExVarBlock( vars, f ) =>
          vars == List( x, y, z )
          f == Pxyz
        case _ => false
      }

      match1 must beTrue
      match2 must beTrue
    }

    "Fail to match other formulas" in {
      exP match {
        case HOLAllVarBlock( _, _ ) => failure
        case _                      =>
      }

      allP match {
        case HOLExVarBlock( _, _ ) => failure
        case _                     =>
      }

      Pxyz match {
        case HOLAllVarBlock( _, _ ) | HOLExVarBlock( _, _ ) => failure
        case _ =>
      }

      success
    }
  }
}
