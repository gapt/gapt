/*
 * BetaReductionTest.scala
 *
 */

package at.logic.language.lambda

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import types._
import symbols._
import BetaReduction._
import StrategyOuterInner._
import StrategyLeftRight._
import ImplicitStandardStrategy._

@RunWith(classOf[JUnitRunner])
class BetaReductionTest extends SpecificationWithJUnit {

  val v = Var("v", Ti); 
  val x = Var("x", Ti); 
  val y = Var("y", Ti);
  val f = Var("f", Ti -> Ti); 
  val g = Var("g", Ti -> Ti)
  val f2 = Var("f2", Ti -> Ti); 
  val g2 = Var("g2", Ti -> Ti)

  "BetaReduction" should {
    "betaReduce a simple redex" in {
        val e = App(Abs(x, App(f, x)),v)
        ( betaReduce(e)(Outermost, Leftmost) ) must beEqualTo ( App(f, v) )
    }
    "betaReduce correctly with outermost strategy" in {
        val e = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        ( betaReduce(e)(Outermost, Leftmost) ) must beEqualTo ( App(Abs(x, App(f, x)),y) )
    }
    "betaReduce correctly with innermost strategy" in {
        val e = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        ( betaReduce(e)(Innermost, Leftmost) ) must beEqualTo ( App(Abs(v, App(f, v)),y) )
    }
    "betaReduce correctly with leftmost strategy" in {
        val er = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        val el = Abs(v, App(Abs(x, App(f, x)),v))
        val e = App(el,er)
        ( betaReduce(e)(Innermost, Leftmost) ) must beEqualTo ( App(Abs(v, App(f, v)),er) )
    }
    "betaReduce correctly with rightmost strategy" in {
        val er = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        val el = Abs(v, App(Abs(x, App(f, x)),v))
        val e = App(el,er)
        ( betaReduce(e)(Innermost, Rightmost) ) must beEqualTo ( App(el,App(Abs(v, App(f, v)),y)) )
    }
    "betaNormalize correctly with outermost strategy" in {
      "- 1" in {
          val er = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
          val el = Abs(v, App(Abs(x, App(f, x)),v))
          val e = App(el,er)
          ( betaNormalize(e)(Outermost) ) must beEqualTo ( App(f,App(f,y)) )
      }
      "- 2" in {
          val e = App(App(Abs(g, Abs(y, App(g,y))), f), v)
          ( betaNormalize(e)(Outermost) ) must beEqualTo ( App(f,v) )
      }
      "- 3" in {
          val e = App(App(App(Abs(g2, Abs(g, Abs(y, App(g2,App(g,y))))), f2), f), v)
          ( betaNormalize(e)(Outermost) ) must beEqualTo ( App(f2,App(f,v)) )
      }
    }
    "betaNormalize correctly with innermost strategy" in {
        val er = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        val el = Abs(v, App(Abs(x, App(f, x)),v))
        val e = App(el,er)
        ( betaNormalize(e)(Innermost) ) must beEqualTo ( App(f,App(f,y)) )
    }
    "betaNormalize correctly with implicit standard strategy" in {
        val er = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        val el = Abs(v, App(Abs(x, App(f, x)),v))
        val e = App(el,er)
        ( betaNormalize(e) ) must beEqualTo ( App(f,App(f,y)) )
    }
    "betaReduce correctly with implicit standard strategy" in {
        val e = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        ( betaReduce(e) ) must beEqualTo ( App(Abs(x, App(f, x)),y) )
    }
    "betaReduce correctly the terms" in {
      "- 1" in {
        val term1 = App(Abs(Var("x",Ti->Ti),Abs(Var("y",Ti),App(Var("x",Ti->Ti),Var("y",Ti)))),Abs(Var("z",Ti),Var("z",Ti)))
        val term2 = Abs(Var("y",Ti),App(Abs(Var("z",Ti),Var("z",Ti)),Var("y",Ti)))
        (betaReduce(term1)(Outermost, Leftmost)) must beEqualTo (term2)
      }
      "- 2" in {
        val term1 = App(Abs(Var("x",Ti->Ti),Abs(Var("x",Ti),App(Var("x",Ti->Ti),Var("x",Ti)))),Abs(Var("x",Ti),Var("x",Ti)))
        val term2 = Abs(Var("y",Ti),App(Abs(Var("z",Ti),Var("z",Ti)),Var("y",Ti)))
        (betaReduce(term1)(Outermost, Leftmost)) must beEqualTo (term2)
      }
      "- 3" in {
        val x1 = Var("x",Ti->Ti)
        val x2 = Var("y",Ti)
        val x3 = Var("z",Ti)
        val x4 = Var("w",Ti)
        val x5 = Var("v",Ti)
        val c1 = Var("f", Ti->(Ti->Ti))
        val t1 = App(c1,App(x1,x2))
        val t2 = App(t1,App(x1,x3))
        val t3 = Abs(x4,x4)
        val term1 = App(Abs(x1::x2::x3::Nil, t2),t3)
        val term2 = Abs(x2::x3::Nil, App(App(c1,App(t3,x2)),App(t3,x3)))
        (betaReduce(term1)(Outermost, Leftmost)) must beEqualTo (term2)
      }
      "- 4" in {
        val e = Abs(x, App(Abs(g, App(g,x)), f))
        (betaReduce(e)(Outermost, Leftmost)) must beEqualTo (Abs(y, App(f, y)))
      }
    }
    "betaNormalize correctly with Abs terms built from variables obtained by the Abs extractor" in {
      val x = Var("x", Ti)
      val y = Var("", Ti)
      val p = Var("p", Ti -> To)
      val px = App( p, x )
      val py = App( p, y )
      val xpx = Abs(x, px)
      val res = xpx match {
        case Abs(v, t) => App(Abs(v, t), y)
      }
      betaNormalize( res )(Innermost) must beEqualTo( py )
    }
    "betaNormalize correctly including a simple variable renaming" in {
      val x = Var( "x", Ti )
      val z = Var( "z", Ti )
      val f = Const( "f", Ti->(Ti->Ti) )
      val M = App( Abs( x::z::Nil, App( f, x::z::Nil )), z )
      val N = Abs( x, App( f, z::x::Nil ))
      val M_normalized = betaNormalize( M )

      M_normalized must beEqualTo ( N )
    }
    "betaNormalize correctly 1+2=3 using Church numerals" in {
      val x = Var( "x", Ti )
      val f = Var( "f", Ti->Ti )
      // a church numeral is of type (Ti->Ti)->(Ti->Ti)
      val m = Var( "m", (Ti->Ti)->(Ti->Ti) )
      val n = Var( "n", (Ti->Ti)->(Ti->Ti) )

      val one = Abs( f::x::Nil, App( f, x ))
      val two = Abs( f::x::Nil, App( f, App( f, x )))
      val three = Abs( f::x::Nil, App( f, App( f, App( f, x ))))

      val add = Abs( m::n::f::x::Nil, App( m, f::App( n, f::x::Nil )::Nil ) )

      val result = betaNormalize( App( add, one::two::Nil ))

      ( result ) must beEqualTo ( three )
    }
    "betaNormalize correctly 8+3=11 using Church numerals" in {
      val x = Var( "x", Ti )
      val f = Var( "f", Ti->Ti )
      // a church numeral is of type (Ti->Ti)->(Ti->Ti)
      val m = Var( "m", (Ti->Ti)->(Ti->Ti) )
      val n = Var( "n", (Ti->Ti)->(Ti->Ti) )

      val three = Abs( f::x::Nil, App( f, App( f, App( f, x ))))
      val eight = Abs( f::x::Nil, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, x )))))))))
      val eleven = Abs( f::x::Nil, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, x ))))))))))))

      val add = Abs( m::n::f::x::Nil, App( m, f::App( n, f::x::Nil )::Nil ) )

      val result = betaNormalize( App( add, eight::three::Nil ))

      ( result ) must beEqualTo ( eleven )
    }
    "betaNormalize correctly 2^3=8 using Church numerals" in {
      val x = Var( "x", Ti )
      val f = Var( "f", Ti->Ti )
      val two = Abs( f::x::Nil, App( f, App( f, x )))
      val eight = Abs( f::x::Nil, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, x )))))))))

      val y = Var( "y", Ti->Ti )
      val g = Var( "g", (Ti->Ti)->(Ti->Ti) )
      val to_power_three = Abs( g::y::Nil, App( g, App( g, App( g, y ))))

      val result = betaNormalize( App( to_power_three, two ))

      ( result ) must beEqualTo ( eight )
    }
  }
}
