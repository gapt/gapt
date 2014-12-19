/*
 * LambdaCalculusTest.scala
 */

package at.logic.language.lambda

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import types._
import symbols._
import scala.collection.immutable.{HashSet, HashMap}
import scala.math.signum

@RunWith(classOf[JUnitRunner])
class LambdaCalculusTest extends SpecificationWithJUnit {
  
  "TypedLambdaCalculus" should {
    "make implicit conversion from String to Name" in {
      (Var("p",Ti) ) must beEqualTo (Var("p", Ti ))
    }
    "create N-ary abstractions (AbsN) correctly" in {
      val v1 = Var("x",Ti)
      val v2 = Var("y",Ti)
      val f = Var("f",Ti -> (Ti -> To))
      ( Abs(v1::v2::Nil, f) match {
        case Abs(v1,Abs(v2,f)) => true
        case _ => false
        }) must beEqualTo ( true )
    }
    "create N-ary applications (AppN) correctly" in {
      val v1 = Var("x",Ti)
      val v2 = Var("y",Ti)
      val f = Var("f",Ti -> (Ti -> To))
      ( App(f, List(v1,v2)) match {
        case App(App(f, v1), v2) => true
        case _ => false
        }) must beEqualTo ( true )
    }
  }
  
  "Equality" should {
    "distinguish variables with same name but different type" in {
      val xi = Var( "x", Ti )
      val xii = Var( "x", Ti->Ti )

      ( xi ) must not be equalTo ( xii )
      ( xi.syntaxEquals( xii )) must beEqualTo ( false )
    }

    "distinguish the constant x from the variable x" in {
      val x_const = Const( "x", Ti )
      val x_var = Var( "x", Ti )

      ( x_const ) must not be equalTo ( x_var )
      ( x_const.syntaxEquals( x_var )) must beEqualTo ( false )
    }

    "equate variables with same name (but different symbols)" in {
      val v = Var( "v", Ti )
      val v0 = Var( "v0", Ti )
      val v_renamed = rename(v, List( v ))

      v_renamed must beEqualTo ( v0 )
      ( v_renamed.syntaxEquals( v0 ) ) must beEqualTo ( true )
    }

    "work correctly for alpha conversion" in {
      val a0 = Abs(Var("x", Ti->Ti), App(Var("x",Ti->Ti),Var("y",Ti)))
      val b0 = Abs(Var("x", Ti->Ti), App(Var("x",Ti->Ti),Var("y",Ti)))
      "- (\\x.xy) = (\\x.xy)" in {
        (a0) must beEqualTo (b0)
        ( a0.syntaxEquals(b0) ) must beEqualTo ( true )
      }
      val a1 = Abs(Var("y", Ti), App(Var("x",Ti->Ti), Var("y", Ti)))
      val b1 = Abs(Var("z", Ti), App(Var("x",Ti->Ti), Var("z", Ti)))
      "- (\\y.xy) = (\\z.xz)" in {
        (a1) must beEqualTo (b1)
        ( a1.syntaxEquals(b1) ) must beEqualTo ( false )
      }
      val a2 = Abs(Var("y", Ti), a1)
      val b2 = Abs(Var("w", Ti), a1)
      "- (\\y.\\y.xy) = (\\w.\\y.xy)" in {
        (a2) must beEqualTo (b2)
        ( a2.syntaxEquals(b2) ) must beEqualTo ( false )
      }
      val a3 = Abs(Var("y", Ti), App(Abs(Var("y", Ti), Var("x", Ti)), Var("y", Ti)))
      val b3 = Abs(Var("w", Ti), App(Abs(Var("y", Ti), Var("x", Ti)), Var("w", Ti)))
      "- (\\y.(\\y.x)y) = (\\w.(\\y.x)w)" in {
        (a3) must beEqualTo (b3)
        ( a3.syntaxEquals(b3) ) must beEqualTo ( false )
      }
      val a4 = Abs(Var("y", Ti), App(Abs(Var("y", Ti), Var("x", Ti)), Var("y", Ti)))
      val b4 = Abs(Var("y", Ti), App(Abs(Var("y", Ti), Var("x", Ti)), Var("w", Ti)))
      "- (\\y.(\\y.x)y) != (\\y.(\\y.x)w)" in {
        (a4) must not be equalTo (b4)
        ( a4.syntaxEquals(b4) ) must beEqualTo ( false )
      }
      val a5 = Abs(Var("y", Ti), App(Abs(Var("y", Ti), Var("y", Ti)), Var("y", Ti)))
      val b5 = Abs(Var("y", Ti), App(Abs(Var("w", Ti), Var("w", Ti)), Var("y", Ti)))
      "- (\\y.(\\y.y)y) = (\\y.(\\w.w)y)" in {
        (a5) must beEqualTo (b5)
        ( a5.syntaxEquals(b5) ) must beEqualTo ( false )
      }
      val a6 = Abs(Var("y", Ti), App(Abs(Var("y", Ti), Var("y", Ti)), Var("y", Ti)))
      val b6 = Abs(Var("y", Ti), App(Abs(Var("w", Ti), Var("y", Ti)), Var("x", Ti)))
      "- (\\y.(\\y.y)y) != (\\y.(\\w.y)y)" in {
        (a6) must not be equalTo (b6)
        ( a6.syntaxEquals(b6) ) must beEqualTo ( false )
      }
    }
  }

  "Hash Codes" should {
    "be equal for alpha equal terms" in {
      val t1 = App(Const("P", Ti -> To), Var("x", Ti))
      val t2 = App(Const("P", Ti -> To), Var("y", Ti))
      val t3 = Abs( Var("x", Ti), t1)
      val t4 = Abs( Var("y", Ti), t2)
      val t5 = Abs( Var("x", Ti), t1)
      val t6 = Abs( Var("y", Ti), t2)

      val l = List(t1,t2,t3,t4,t5,t6)
      l.forall(x => l.forall(y => {
        if (x == y)
          x.hashCode() must_== y.hashCode()
        else
          true
      }))

      ok("all tests passed")
    }

    "make maps and sets properly defined" in {
      val t1 = App(Const("P", Ti -> To), Var("x", Ti))
      val t2 = App(Const("P", Ti -> To), Var("y", Ti))
      val t3 = Abs( Var("x", Ti), t1)
      val t4 = Abs( Var("y", Ti), t2)
      val t5 = Abs( Var("x", Ti), t1)
      val t6 = Abs( Var("y", Ti), t2)

      val map = HashMap[LambdaExpression, Int]()
      val set = HashSet[LambdaExpression]()

      val nmap = map + ((t3,1)) + ((t4,2))
      nmap(t3) must_==(2) //the entry for the alpha equal formula must have been overwritten
      nmap.size must_==(1) //t3 and t4 are considered equal, so the keyset must not contain both
      nmap must beEqualTo( Map[LambdaExpression, Int]() + ((t3,1)) + ((t4,2))) //map and hashmap must agree

      val nset = set + t3 + t4
      nset.size must_==(1) //t3 and t4 are considered equal, so the set must not contain both
      nset must beEqualTo( Set() + t3 + t4 ) //hashset and set must agree
    }

  }

  "Variable renaming" should {
    "produce a new variable different from all in the blacklist" in {
      val x = Var( "x", Ti )
      val y = Var( "y", Ti )
      val z = Var( "z", Ti )
      val blacklist = x::y::z::Nil
      val x_renamed = rename( x, blacklist )

      ( blacklist.contains( x_renamed ) ) must beEqualTo ( false )
    }

    "produce a new variable different from all in the blacklist (in presence of maliciously chosen variable names)" in {
      val v = Var( "v", Ti )
      val v0 = Var( "v0", Ti )
      val v_renamed = rename( v, v::v0::Nil )
   
      ( v_renamed ) must not be equalTo ( v0 )
      ( v_renamed.syntaxEquals( v0 ) ) must beEqualTo ( false )
    }
  }

  "TypedLambdaCalculus" should {
    "extract free variables correctly" in {
      val x = Var("X", Ti -> To )
      val y = Var("y", Ti )
      val z = Var("Z", Ti -> To )
      val r = Var("R", (Ti -> To) -> (Ti -> ((Ti -> To) -> To)))
      val a = App(r, x::y::z::Nil)
      val qa = Abs( x, a )
      val free = freeVariables(qa)
      free must not (contain( (v: Var) => v.syntaxEquals(x) ))
      free must (contain( (v: Var) => v.syntaxEquals(y) ))
      free must (contain( (v: Var) => v.syntaxEquals(z) ))
      free must (contain( (v: Var) => v.syntaxEquals(r) ))
    }

    "extract free variables correctly" in {
      val x = Var( "x", Ti -> Ti )
      val z = Var( "z", Ti )
      val M = App( Abs( x, App( x, z )), x )

      val fv = freeVariables(M).toSet
      val fv_correct = Set( x, z )

      fv must be equalTo( fv_correct )
    }

    "extract free variables correctly" in {
      val x = Var( "x", Ti -> Ti )
      val z = Var( "z", Ti )
      val M = Abs( x, App( Abs( x, App( x, z )), x ))

      val fv = freeVariables(M).toSet
      val fv_correct = Set( z )

      fv must be equalTo( fv_correct )
    }

    "deal correctly with bound variables in the Abs extractor" in {
      val x = Var("x", Ti)
      val p = Var("p", Ti -> To)
      val px = App(p, x)
      val xpx = Abs(x, px)

      val res = xpx match {
        case Abs(v, t) => Abs(v, t)
      } 

      res must beEqualTo( xpx )
    }
  }
}
