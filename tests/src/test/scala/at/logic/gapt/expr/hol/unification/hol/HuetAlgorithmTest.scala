/*
 * HuetAlgorithmTest.scala
 *
 */

/*
package at.logic.gapt.language.hol.algorithms.unification.hol


import at.logic.gapt.language.hol.algorithms.unification.hol.huet._
import at.logic.gapt.expr.BetaReduction
import at.logic.gapt.expr.BetaReduction._
import scala.collection.immutable.HashMap
import at.logic.gapt.expr.substitutions.Substitution
import org.specs2.mutable._
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.gapt.language.hol.algorithms.unification.hol._
import at.logic.gapt.language.hol._
import at.logic.gapt.expr._
import logicSymbols._
import at.logic.gapt.expr._
import at.logic.gapt.expr.typedLambdaCalculus._
import logicSymbols.ImplicitConverters._
import at.logic.gapt.expr.Definitions._
import at.logic.gapt.expr.ImplicitConverters._
import StrategyOuterInner._
import StrategyLeftRight._


//private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser

class HuetAlgorithmTest extends Specification with org.specs2.ScalaCheck {
    "HuetAlgorithm" should {

//       class MyParser(input: String) extends StringReader(input) with SimpleHOLParser

      val a = Const(new ConstantStringSymbol("a"), i)
      val b= Const(new ConstantStringSymbol("b"), i)
      val c= Const(new ConstantStringSymbol("c"), i)
      val d= Const(new ConstantStringSymbol("d"), i)

      val x = Var("x", i)
      val F = Var("F", i->i)
      val y = Var("y", i)
      val z = Var("z", i)
      val f = Const(new ConstantStringSymbol("f"), i->i)
      val fa = App(f, a)
      val fb= App(f, b)
      val fx= App(f, x)

      val g = Const(new ConstantStringSymbol("g"), i->(i->i))
//      val h = Const(new ConstantStringSymbol("h"), i->(i->i))

      val Fa = App(F,a)
      val Ffa = App(F,App(f,a))

      val fFa = App(f,App(F,a))
      val gfFafFa = App(App(g, fFa), fFa)
      val gFaFa = App(App(g, Fa), Fa)
      val gaa = App(App(g, a), a)
      val ga = App(g, a)
      val gax = App(App(g, a), x)
      val fgaa = App(f,gaa)
      val fgax = App(f,gax)
      val ffa = App(f,fa)
      val fz = App(f, z)
      val fy = App(f, y)
      val gfafa = App(App(g, fa), fa)
      val gfbfa = App(App(g, fb), fa)

      val gfafx = App(App(g, fa), fx)
      val gfbfx = App(App(g, fb), fx)
      val gfYfX = App(App(g, fy), fx)

      val f1 = Const(new ConstantStringSymbol("f1"), i->(i->(i->(i->i))))
      val f2 = Const(new ConstantStringSymbol("f2"), (i->(i->i)))
      val h1 = Const(new ConstantStringSymbol("h1"), i->i)

      val f2xgay = App(App(f2, x), App(App(g,a),y))
      val f2xgyx = App(App(f2, x), App(App(g,y),x))

      val xgax = Abs(x,gax)
      val Fx = App(F,x)
      val xFx = Abs(x,Fx)
      val H1 = Var("H1", i->i)
      val H2 = Var("H2", i->i)
      val h1Fa = App(h1,Fa)
//      val t = Abs(x, App(App(g, App(H1, x)),App(H2,x))).asInstanceOf[LambdaExpression]

//              val h = Huet((x,c)::(a,y)::Nil)
//              val h = Huet((fy,fz)::(fz,fa)::Nil)
//              val h = Huet((fy,fz)::Nil)
//                val h = Huet((xFx,xfx)::Nil)
//              val h = Huet((xFx,xgax)::Nil)


      val dnLine = sys.props("line.separator") + sys.props("line.separator")
//              val h = Huet((Fa, gaa)::Nil)
//              val nxt = h.next
//              nxt match {
//                case None => println( dnLine + " None!")
//                case _ => println( dnLine + "rez = "+nxt.get.toString)
//              }
//              println(dnLine+h.next.get.toString)// ; "+ st.next.get.toString)

      "fail on unifying two different constants" in {
       Huet(c,d).next must beEqualTo (None    )
      }

      "return an empty substitution on two identical constants" in {
        Huet(c,c).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()))
      }

      "return an empty substitution {x->c} on <x,c>" in {
        Huet(x,c).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(x,c)))
      }

      "return an empty substitution {x->c} on <c,x>" in {
        Huet(c,x).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(x,c)))
      }

      "fail on <fa,fb>" in {
        Huet(fa,fb).next must beEqualTo (None)
      }

      "fail on <fa,gaa>" in {
        Huet(fa,gaa).next must beEqualTo (None)
      }

      "return a sub. on <fz, fa>" in {
        Huet(fz,fa).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(z,a)))
      }

      "return a sub. on <fa, fz>" in {
        Huet(fa,fz).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(z,a)))
      }

//       "fail on <F: i->i, gaa : i> because of different types" in {
//        Huet(F,gaa).next must beEqualTo (None)
//      }


      "return a subst. {y->fz} on <y, fz>" in {
        Huet(y,fz).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(y,fz)))
      }

      "return a subst. {x->y} on <x,y>" in {
        Huet(x,y).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(x,y)))
      }


      "return a subst. {x->a} on <fgaa,fgax>" in {
        Huet(fgax,fgaa).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(x,a)))
      }

      "return a subst. {x->a} on <gfafx,gfafa>" in {
        Huet(gfafx,gfafa).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(x,a)))
      }

      "return a subst. {x->a} on <gfafa,gfafx>" in {
        Huet(gfafa,gfafx).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(x,a)))
      }

      "fail on <gfafa,gfbfx>" in {
        Huet(gfafa,gfbfx).next must beEqualTo (None)
      }

      "return a subst. on <gfbfa,gfyfx>" in {
        Huet(gfbfa,gfYfX).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(x,a)+Pair(y,b)))
      }

      "return a subst. on <gfyfx, gfbfa>" in {
        Huet(gfYfX, gfbfa).next.get must beEqualTo (Substitution[LambdaExpression](new HashMap[Var, LambdaExpression]()+Pair(x,a)+Pair(y,b)))
      }

      "return a sub. on <fFa,Ffa>" in {
        val h = Huet(Ffa, fFa)
        val nx = h.next.get
        val nx1 = h.next.get
        Huet.applySubToListOfPairs(Pair(Ffa,Ffa)::Nil, nx) must beEqualTo (Huet.applySubToListOfPairs(Pair(fFa,fFa)::Nil, nx))
        Huet.applySubToListOfPairs(Pair(Ffa,Ffa)::Nil, nx1) must beEqualTo (Huet.applySubToListOfPairs(Pair(fFa,fFa)::Nil, nx1))
      }


//      " NOT terminate on <F(f(a)),g(F(a))>" in {
//        val a = Const(new ConstantStringSymbol("a"), i)
//        val F = Var("F", i->i)
//        val g = Const(new ConstantStringSymbol("g"), i->i)
//        val f = Const(new ConstantStringSymbol("f"), i->i)
//
//        val fa = App(f,a)
//        val Fa = App(F,a)
//        val Ffa = App(F,fa)
//        val gFa = App(g,Fa)
//
//        val uprobl = Tuple2(Ffa, gFa)::Nil
//        val h = Huet(uprobl)
//        val sub = h.next.get
//        println( dnLine + "sub = "+sub.toString)
////        val rez = Huet.applySubToListOfPairs(uprobl, sub)
////        println( dnLine + "rez after sub = "+rez.toString)
//        println( dnLine + "rez = "+h.next.get.toString)
//        println( dnLine + "rez = "+h.next.toString)
////        println("eta <F,ga> = "+Huet.etaBetaNormalization(Tuple2(F,ga)::Nil))
////        Huet.applySubToListOfPairs(Pair(Ffa,Ffa)::Nil, nx) must beEqualTo (Huet.applySubToListOfPairs(Pair(fFa,fFa)::Nil, nx))
//        0 must beEqualTo (0)
//      }


      " return a sub. on <FX,g(F(a))>" in {
        val a = Const(new ConstantStringSymbol("a"), i)
        val F = Var("F", i->i)
        val g = Const(new ConstantStringSymbol("g"), i->i)
        val f = Const(new ConstantStringSymbol("f"), i->i)
        val X = Var("X", i)

        val FX = App(F,X)

        val gFa = App(g,Fa)

        val uprobl = Tuple2(FX, gFa)::Nil
        val h = Huet(uprobl)
        val nx = h.next.get
//        println( dnLine + "sub = "+sub.toString)

        Huet.applySubToListOfPairs(Pair(FX,FX)::Nil, nx) must beEqualTo (Huet.applySubToListOfPairs(Pair(gFa,gFa)::Nil, nx))
      }
    }
}
*/
