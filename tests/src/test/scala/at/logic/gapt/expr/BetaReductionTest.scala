/*
 * BetaReductionTest.scala
 *
 */

package at.logic.gapt.expr

import org.specs2.mutable._

class BetaReductionTest extends Specification {

  val v = Var( "v", Ti );
  val x = Var( "x", Ti );
  val y = Var( "y", Ti );
  val f = Var( "f", Ti ->: Ti );
  val g = Var( "g", Ti ->: Ti )
  val f2 = Var( "f2", Ti ->: Ti );
  val g2 = Var( "g2", Ti ->: Ti )

  "BetaReduction" should {
    "normalize correctly with outermost strategy" in {
      "- 1" in {
        val er = App( Abs( v, App( Abs( x, App( f, x ) ), v ) ), y )
        val el = Abs( v, App( Abs( x, App( f, x ) ), v ) )
        val e = App( el, er )
        normalize( e ) must_== App( f, App( f, y ) )
      }
      "- 2" in {
        val e = App( App( Abs( g, Abs( y, App( g, y ) ) ), f ), v )
        normalize( e ) must_== App( f, v )
      }
      "- 3" in {
        val e = App( App( App( Abs( g2, Abs( g, Abs( y, App( g2, App( g, y ) ) ) ) ), f2 ), f ), v )
        normalize( e ) must_== App( f2, App( f, v ) )
      }
    }
    "normalize correctly with innermost strategy" in {
      val er = App( Abs( v, App( Abs( x, App( f, x ) ), v ) ), y )
      val el = Abs( v, App( Abs( x, App( f, x ) ), v ) )
      val e = App( el, er )
      normalize( e ) must_== App( f, App( f, y ) )
    }
    "normalize correctly with implicit standard strategy" in {
      val er = App( Abs( v, App( Abs( x, App( f, x ) ), v ) ), y )
      val el = Abs( v, App( Abs( x, App( f, x ) ), v ) )
      val e = App( el, er )
      normalize( e ) must_== App( f, App( f, y ) )
    }
    "normalize correctly with Abs terms built from variables obtained by the Abs extractor" in {
      val x = Var( "x", Ti )
      val y = Var( "", Ti )
      val p = Var( "p", Ti ->: To )
      val px = App( p, x )
      val py = App( p, y )
      val xpx = Abs( x, px )
      val res = xpx match {
        case Abs( v, t ) => App( Abs( v, t ), y )
      }
      normalize( res ) must_== py
    }
    "normalize correctly including a simple variable renaming" in {
      val x = Var( "x", Ti )
      val z = Var( "z", Ti )
      val f = Const( "f", Ti ->: Ti ->: Ti )
      val M = App( Abs( x :: z :: Nil, App( f, x :: z :: Nil ) ), z )
      val N = Abs( x, App( f, z :: x :: Nil ) )
      val M_normalized = normalize( M )

      M_normalized must_== N
    }
    "normalize correctly 1+2=3 using Church numerals" in {
      val x = Var( "x", Ti )
      val f = Var( "f", Ti ->: Ti )
      // a church numeral is of type (Ti->Ti)->(Ti->Ti)
      val m = Var( "m", ( Ti ->: Ti ) ->: Ti ->: Ti )
      val n = Var( "n", ( Ti ->: Ti ) ->: Ti ->: Ti )

      val one = Abs( f :: x :: Nil, App( f, x ) )
      val two = Abs( f :: x :: Nil, App( f, App( f, x ) ) )
      val three = Abs( f :: x :: Nil, App( f, App( f, App( f, x ) ) ) )

      val add = Abs( m :: n :: f :: x :: Nil, App( m, f :: App( n, f :: x :: Nil ) :: Nil ) )

      val result = normalize( App( add, one :: two :: Nil ) )

      result must_== three
    }
    "normalize correctly 8+3=11 using Church numerals" in {
      val x = Var( "x", Ti )
      val f = Var( "f", Ti ->: Ti )
      // a church numeral is of type (Ti->Ti)->(Ti->Ti)
      val m = Var( "m", ( Ti ->: Ti ) ->: Ti ->: Ti )
      val n = Var( "n", ( Ti ->: Ti ) ->: Ti ->: Ti )

      val three = Abs( f :: x :: Nil, App( f, App( f, App( f, x ) ) ) )
      val eight = Abs( f :: x :: Nil, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, x ) ) ) ) ) ) ) ) )
      val eleven = Abs( f :: x :: Nil, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, x ) ) ) ) ) ) ) ) ) ) ) )

      val add = Abs( m :: n :: f :: x :: Nil, App( m, f :: App( n, f :: x :: Nil ) :: Nil ) )

      val result = normalize( App( add, eight :: three :: Nil ) )

      result must_== eleven
    }
    "normalize correctly 2^3=8 using Church numerals" in {
      val x = Var( "x", Ti )
      val f = Var( "f", Ti ->: Ti )
      val two = Abs( f :: x :: Nil, App( f, App( f, x ) ) )
      val eight = Abs( f :: x :: Nil, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, x ) ) ) ) ) ) ) ) )

      val y = Var( "y", Ti ->: Ti )
      val g = Var( "g", ( Ti ->: Ti ) ->: Ti ->: Ti )
      val to_power_three = Abs( g :: y :: Nil, App( g, App( g, App( g, y ) ) ) )

      val result = normalize( App( to_power_three, two ) )

      result must_== eight
    }
  }
  "issue 659" in {
    normalize( le"(^y y) y x" ) must_== le"y x"
  }
}
