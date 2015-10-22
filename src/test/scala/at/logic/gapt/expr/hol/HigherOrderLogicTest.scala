/*
 * HigherOrderLogicTest.scala
 */

package at.logic.gapt.expr.hol

import org.specs2.mutable._
import at.logic.gapt.expr._
import BetaReduction._

class HigherOrderLogicTest extends Specification {

  "HigherOrderLogic" should {
    val c1 = Const( "a", Ti -> To )
    val v1 = Var( "x", Ti )
    val a1 = App( c1, v1 )
    val c2 = Var( "a", Ti -> ( Ti -> To ) )
    val v21 = Var( "x", Ti )
    val v22 = Var( "y", Ti )
    val a21 = App( c2, v21 )
    val a22 = App( a21, v22 )

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
      val at1 = HOLAtom( Var( "P", ( c2.exptype -> ( a22.exptype -> To ) ) ), c2 :: a22 :: Nil )
      // Another way to construct P's type is: FunctionType(To, args.map(a => a.exptype) )
      val result = at1 match {
        case x: HOLFormula => true
        case _             => false
      }
      result must beTrue
    }
    "And connective should return the right And formula" in {
      val c1 = HOLAtom( Const( "a", To ) )
      val c2 = HOLAtom( Const( "b", To ) )
      val result = And( c1, c2 ) match {
        case App( App( andC, c1 ), c2 ) => true
        case _                          => false
      }
      result must beTrue
    }
    "Or connective should return the right formula" in {
      val c1 = HOLAtom( Const( "a", To ) )
      val c2 = HOLAtom( Const( "b", To ) )
      val result = Or( c1, c2 ) match {
        case App( App( orC, c1 ), c2 ) => true
        case _                         => false
      }
      result must beTrue
    }
    "Imp connective should return the right formula" in {
      val c1 = HOLAtom( Var( "a", To ) )
      val c2 = HOLAtom( Var( "b", To ) )
      val result = Imp( c1, c2 ) match {
        case App( App( impC, c1 ), c2 ) => true
        case _                          => false
      }
      result must beTrue
    }
    "Neg connective should " in {
      "return the right formula" in {
        val c1 = HOLAtom( Var( "a", To ) )
        val result = Neg( c1 ) match {
          case App( negC, c1 ) => true
          case _               => false
        }
        result must beTrue
      }
      "be extracted correctly" in {
        val e = App( Const( "g", Ti -> Ti ), Const( "c", Ti ) :: Nil )
        val result = e match {
          case Neg( _ ) => false
          case _        => true
        }
        result must beTrue
      }
    }

    "substitute and normalize correctly when Substitution is applied" in {
      val x = Var( "X", Ti -> To )
      val f = Var( "f", ( Ti -> To ) -> Ti )
      val xfx = App( x, App( f, x ) )

      val z = Var( "z", Ti )
      val p = Var( "P", Ti -> To )
      val Pz = App( p, z )
      val t = Abs( z, Pz )
      val pft = App( p, App( f, t ) )

      val sigma = Substitution( x, t )

      betaNormalize( sigma( xfx ) ) must beEqualTo( pft )
    }

    "substitute and normalize correctly when Substitution is applied on the formula level" in {
      val x = Var( "X", Ti -> To )
      val f = Var( "f", ( Ti -> To ) -> Ti )
      val xfx = HOLAtom( x, HOLFunction( f, x :: Nil ) :: Nil )

      val z = Var( "z", Ti )
      val p = Var( "P", Ti -> To )
      val Pz = App( p, z )
      val t = Abs( z, Pz )
      val pft = HOLAtom( p, HOLFunction( f, t :: Nil ) :: Nil )

      val sigma = Substitution( x, t )
      val xfx_sigma = betaNormalize( sigma( xfx ) )

      xfx_sigma must beEqualTo( pft )
    }
  }

  "Exists quantifier" should {
    val c1 = Const( "a", Ti -> To )
    val v1 = Var( "x", Ti )
    val f1 = HOLAtom( c1, v1 :: Nil )
    "create a term of the right type" in {
      ( Ex( v1, f1 ).exptype ) must beEqualTo( To )
    }
  }

  "Forall quantifier" should {
    val c1 = Const( "a", Ti -> To )
    val v1 = Var( "x", Ti )
    val f1 = HOLAtom( c1, v1 :: Nil )
    "create a term of the right type" in {
      ( All( v1, f1 ).exptype ) must beEqualTo( To )
    }
  }

  "Atoms" should {
    "be extracted correctly" in {
      val p = Const( "P", To )
      val result = p match {
        case HOLAtom( Const( "P", To ), Nil ) => true
        case _                                => false
      }
      result must beTrue
    }
  }

  "Equation" should {
    "be of the right type" in {
      val c1 = Const( "f1", Ti -> Ti )
      val c2 = Const( "f2", Ti -> Ti )
      val eq = Eq( c1, c2 )
      val App( App( t, _ ), _ ) = eq
      t.exptype must beEqualTo( ( Ti -> Ti ) -> ( ( Ti -> Ti ) -> To ) )
    }
  }

  "Substitution" should {
    "work correctly on some testcase involving free/bound vars" in {
      val s0 = Const( "s_{0}", Ti -> Ti )
      val C = Const( "C", Ti -> Ti )
      val T = Const( "T", Ti -> Ti )
      val sCTn = HOLFunction( s0, HOLFunction( C, HOLFunction( T, Const( "n", Ti ) :: Nil ) :: Nil ) :: Nil )
      val u = Var( "u", Ti )
      val v = Var( "v", Ti )
      val P1 = HOLAtom( Var( "P", sCTn.exptype -> ( Ti -> To ) ), sCTn :: u :: Nil )
      val P2 = HOLAtom( Var( "P", sCTn.exptype -> ( Ti -> To ) ), sCTn :: v :: Nil )
      val q_form = All( u, Ex( v, Imp( P1, P2 ) ) )

      q_form match {
        case All( x, f ) => {
          val a = Const( "a", x.exptype )
          val sub = Substitution( x, a )
          val P3 = HOLAtom( Var( "P", sCTn.exptype -> ( a.exptype -> To ) ), sCTn :: a :: Nil )
          val s = sub( f )
          val result = s match {
            case Ex( v, Imp( P3, P2 ) ) => true
            case _                      => false
          }
          result must beTrue
        }
      }
    }
  }

  "SkolemSymbolFactory" should {
    val x = Var( "x", Ti )
    val y = Var( "y", Ti )
    val f = All( x, HOLAtom( Var( "P", Ti -> To ), x :: Nil ) )
    val s0 = new StringSymbol( "s_{0}" )
    val s1 = new StringSymbol( "s_{2}" )
    val s2 = new StringSymbol( "s_{4}" )
    val s3 = new StringSymbol( "s_{6}" )

    val stream = new SkolemSymbolFactory().getSkolemSymbols

    "return a correct stream of Skolem symbols" in {
      stream.head must beEqualTo( s0 )
      stream.tail.head must beEqualTo( s1 )
      stream.tail.tail.head must beEqualTo( s2 )
    }
  }

  "Higher Order Formula matching" should {
    "not allow P and P match as an Atom " in {
      val f = And( HOLAtom( Var( "P", To ), Nil ), HOLAtom( Var( "P", To ), Nil ) )

      f must beLike {
        case HOLAtom( _, _ ) =>
          println( "Is an atom" ); ko
        case HOLFunction( _, _ ) => ko
        case All( _, _ )         => ko
        case Ex( _, _ )          => ko
        case Or( _, _ )          => ko
        case Imp( _, _ )         => ko
        case And( _, _ )         => ok
        case _                   => ko
      }
    }
  }

  "Quantifier blocks" should {
    val x = Var( "x", Ti )
    val y = Var( "y", Ti )
    val z = Var( "z", Ti )

    val Pxyz = HOLAtom( Const( "P", Ti -> ( Ti -> ( Ti -> To ) ) ), List( x, y, z ) )
    val allP = All( x, All( y, All( z, Pxyz ) ) )
    val exP = Ex( x, Ex( y, Ex( z, Pxyz ) ) )

    "Correctly introduce one quantifier" in {
      All.Block( List( x ), Pxyz ) must beEqualTo( All( x, Pxyz ) )
      Ex.Block( List( x ), Pxyz ) must beEqualTo( Ex( x, Pxyz ) )
    }

    "Correctly introduce multiple quantifiers" in {
      All.Block( List( x, y, z ), Pxyz ) must beEqualTo( allP )
      Ex.Block( List( x, y, z ), Pxyz ) must beEqualTo( exP )
    }

    "Correctly match quantified formulas" in {

      val match1 = allP match {
        case All.Block( vars, f ) =>
          vars == List( x, y, z )
          f == Pxyz
      }

      val match2 = exP match {
        case Ex.Block( vars, f ) =>
          vars == List( x, y, z )
          f == Pxyz
      }

      match1 must beTrue
      match2 must beTrue
    }

    "Fail to match other formulas" in {
      exP must beLike { case All.Block( List(), _ ) => ok }
      allP must beLike { case Ex.Block( List(), _ ) => ok }
      Pxyz must beLike { case All.Block( List(), _ ) => ok }
      Pxyz must beLike { case Ex.Block( List(), _ ) => ok }
    }
  }
}
