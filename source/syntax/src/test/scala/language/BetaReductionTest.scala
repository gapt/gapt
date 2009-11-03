/*
 * BetaReductionTest.scala
 *
 */

package at.logic.language

import org.specs._
import org.specs.runner._


import Types._
import Symbols._
import Symbols.SymbolImplicitConverters._
import TypedLambdaCalculus._
import Substitutions._
import BetaReduction._



class BetaReductionTest extends Specification with JUnit {
  import StrategyOuterInner._
  import StrategyLeftRight._
  level = Debug  // sets the printing of extra information (level can be: Debug, Info, Warning, Error)

  val v = Var("v", i); val x = Var("x", i); val y = Var("y", i);
  val f = Var("f", i -> i)

  "BetaReduction" should {
    "betaReduce a simple redex" in {
        val e = App(Abs(x, App(f, x)),v)
        ( betaReduce(e)(Outermost, Leftmost) ) must beEqual ( App(f, v) )
    }
    "betaReduce correctly with outermost strategy" in {
        val e = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        ( betaReduce(e)(Outermost, Leftmost) ) must beEqual ( App(Abs(x, App(f, x)),y) )
    }
    "betaReduce correctly with innermost strategy" in {
        val e = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        ( betaReduce(e)(Innermost, Leftmost) ) must beEqual ( App(Abs(v, App(f, v)),y) )
    }
    "betaReduce correctly with leftmost strategy" in {
        val er = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        val el = Abs(v, App(Abs(x, App(f, x)),v))
        val e = App(el,er)
        ( betaReduce(e)(Innermost, Leftmost) ) must beEqual ( App(Abs(v, App(f, v)),er) )
    }
    "betaReduce correctly with rightmost strategy" in {
        val er = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        val el = Abs(v, App(Abs(x, App(f, x)),v))
        val e = App(el,er)
        ( betaReduce(e)(Innermost, Rightmost) ) must beEqual ( App(el,App(Abs(v, App(f, v)),y)) )
    }
    "betaNormalize correctly with outermost strategy" in {
        val er = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        val el = Abs(v, App(Abs(x, App(f, x)),v))
        val e = App(el,er)
        ( betaNormalize(e)(Outermost) ) must beEqual ( App(f,App(f,y)) )
    }
    "betaNormalize correctly with innermost strategy" in {
        val er = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        val el = Abs(v, App(Abs(x, App(f, x)),v))
        val e = App(el,er)
        ( betaNormalize(e)(Innermost) ) must beEqual ( App(f,App(f,y)) )
    }
    "betaNormalize correctly with implicit standard strategy" in {
        import ImplicitStandardStrategy._
        val er = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        val el = Abs(v, App(Abs(x, App(f, x)),v))
        val e = App(el,er)
        ( betaNormalize(e) ) must beEqual ( App(f,App(f,y)) )
    }
    "betaReduce correctly with implicit standard strategy" in {
        import ImplicitStandardStrategy._
        val e = App(Abs(v, App(Abs(x, App(f, x)),v)),y)
        ( betaReduce(e) ) must beEqual ( App(Abs(x, App(f, x)),y) )
    }
  }
}