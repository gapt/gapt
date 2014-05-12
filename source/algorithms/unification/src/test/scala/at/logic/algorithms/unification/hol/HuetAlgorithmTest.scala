/*
 * HuetAlgorithmTest.scala
 *
 */

/*
package at.logic.algorithms.unification.hol


import at.logic.algorithms.unification.hol.huet._
import at.logic.language.lambda.BetaReduction
import at.logic.language.lambda.BetaReduction._
import scala.collection.immutable.HashMap
import at.logic.language.lambda.substitutions.Substitution
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.algorithms.unification.hol._
import at.logic.language.hol._
import at.logic.language.lambda.symbols._
import logicSymbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import logicSymbols.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols.ImplicitConverters._
import StrategyOuterInner._
import StrategyLeftRight._


//private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser

@RunWith(classOf[JUnitRunner])
class HuetAlgorithmTest extends SpecificationWithJUnit with org.specs2.ScalaCheck {
    "HuetAlgorithm" should {

//       class MyParser(input: String) extends StringReader(input) with SimpleHOLParser

      val a = HOLConst(new ConstantStringSymbol("a"), i)
      val b= HOLConst(new ConstantStringSymbol("b"), i)
      val c= HOLConst(new ConstantStringSymbol("c"), i)
      val d= HOLConst(new ConstantStringSymbol("d"), i)

      val x = HOLVar("x", i)
      val F = HOLVar("F", i->i)
      val y = HOLVar("y", i)
      val z = HOLVar("z", i)
      val f = HOLConst(new ConstantStringSymbol("f"), i->i)
      val fa = HOLApp(f, a)
      val fb= HOLApp(f, b)
      val fx= HOLApp(f, x)

      val g = HOLConst(new ConstantStringSymbol("g"), i->(i->i))
//      val h = HOLConst(new ConstantStringSymbol("h"), i->(i->i))

      val Fa = HOLApp(F,a)
      val Ffa = HOLApp(F,HOLApp(f,a))

      val fFa = HOLApp(f,HOLApp(F,a))
      val gfFafFa = HOLApp(HOLApp(g, fFa), fFa)
      val gFaFa = HOLApp(HOLApp(g, Fa), Fa)
      val gaa = HOLApp(HOLApp(g, a), a)
      val ga = HOLApp(g, a)
      val gax = HOLApp(HOLApp(g, a), x)
      val fgaa = HOLApp(f,gaa)
      val fgax = HOLApp(f,gax)
      val ffa = HOLApp(f,fa)
      val fz = HOLApp(f, z)
      val fy = HOLApp(f, y)
      val gfafa = HOLApp(HOLApp(g, fa), fa)
      val gfbfa = HOLApp(HOLApp(g, fb), fa)

      val gfafx = HOLApp(HOLApp(g, fa), fx)
      val gfbfx = HOLApp(HOLApp(g, fb), fx)
      val gfYfX = HOLApp(HOLApp(g, fy), fx)

      val f1 = HOLConst(new ConstantStringSymbol("f1"), i->(i->(i->(i->i))))
      val f2 = HOLConst(new ConstantStringSymbol("f2"), (i->(i->i)))
      val h1 = HOLConst(new ConstantStringSymbol("h1"), i->i)

      val f2xgay = HOLApp(HOLApp(f2, x), HOLApp(HOLApp(g,a),y))
      val f2xgyx = HOLApp(HOLApp(f2, x), HOLApp(HOLApp(g,y),x))

      val xgax = HOLAbs(x,gax)
      val Fx = HOLApp(F,x)
      val xFx = HOLAbs(x,Fx)
      val H1 = HOLVar("H1", i->i)
      val H2 = HOLVar("H2", i->i)
      val h1Fa = HOLApp(h1,Fa)
//      val t = Abs(x, App(App(g, App(H1, x)),App(H2,x))).asInstanceOf[HOLExpression]

//              val h = Huet((x,c)::(a,y)::Nil)
//              val h = Huet((fy,fz)::(fz,fa)::Nil)
//              val h = Huet((fy,fz)::Nil)
//                val h = Huet((xFx,xfx)::Nil)
//              val h = Huet((xFx,xgax)::Nil)


//              val h = Huet((Fa, gaa)::Nil)
//              val nxt = h.next
//              nxt match {
//                case None => println("\n\n None!")
//                case _ => println("\n\nrez = "+nxt.get.toString)
//              }
//              println("\n\n"+h.next.get.toString)// ; "+ st.next.get.toString)

      "fail on unifying two different constants" in {
       Huet(c,d).next must beEqualTo (None    )
      }

      "return an empty substitution on two identical constants" in {
        Huet(c,c).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()))
      }

      "return an empty substitution {x->c} on <x,c>" in {
        Huet(x,c).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,c)))
      }

      "return an empty substitution {x->c} on <c,x>" in {
        Huet(c,x).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,c)))
      }

      "fail on <fa,fb>" in {
        Huet(fa,fb).next must beEqualTo (None)
      }

      "fail on <fa,gaa>" in {
        Huet(fa,gaa).next must beEqualTo (None)
      }

      "return a sub. on <fz, fa>" in {
        Huet(fz,fa).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(z,a)))
      }

      "return a sub. on <fa, fz>" in {
        Huet(fa,fz).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(z,a)))
      }

//       "fail on <F: i->i, gaa : i> because of different types" in {
//        Huet(F,gaa).next must beEqualTo (None)
//      }


      "return a subst. {y->fz} on <y, fz>" in {
        Huet(y,fz).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(y,fz)))
      }

      "return a subst. {x->y} on <x,y>" in {
        Huet(x,y).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,y)))
      }


      "return a subst. {x->a} on <fgaa,fgax>" in {
        Huet(fgax,fgaa).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,a)))
      }

      "return a subst. {x->a} on <gfafx,gfafa>" in {
        Huet(gfafx,gfafa).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,a)))
      }

      "return a subst. {x->a} on <gfafa,gfafx>" in {
        Huet(gfafa,gfafx).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,a)))
      }

      "fail on <gfafa,gfbfx>" in {
        Huet(gfafa,gfbfx).next must beEqualTo (None)
      }

      "return a subst. on <gfbfa,gfyfx>" in {
        Huet(gfbfa,gfYfX).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,a)+Pair(y,b)))
      }

      "return a subst. on <gfyfx, gfbfa>" in {
        Huet(gfYfX, gfbfa).next.get must beEqualTo (Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,a)+Pair(y,b)))
      }

      "return a sub. on <fFa,Ffa>" in {
        val h = Huet(Ffa, fFa)
        val nx = h.next.get
        val nx1 = h.next.get
        Huet.applySubToListOfPairs(Pair(Ffa,Ffa)::Nil, nx) must beEqualTo (Huet.applySubToListOfPairs(Pair(fFa,fFa)::Nil, nx))
        Huet.applySubToListOfPairs(Pair(Ffa,Ffa)::Nil, nx1) must beEqualTo (Huet.applySubToListOfPairs(Pair(fFa,fFa)::Nil, nx1))
      }


//      " NOT terminate on <F(f(a)),g(F(a))>" in {
//        val a = HOLConst(new ConstantStringSymbol("a"), i)
//        val F = HOLVar("F", i->i)
//        val g = HOLConst(new ConstantStringSymbol("g"), i->i)
//        val f = HOLConst(new ConstantStringSymbol("f"), i->i)
//
//        val fa = HOLApp(f,a)
//        val Fa = HOLApp(F,a)
//        val Ffa = HOLApp(F,fa)
//        val gFa = HOLApp(g,Fa)
//
//        val uprobl = Tuple2(Ffa, gFa)::Nil
//        val h = Huet(uprobl)
//        val sub = h.next.get
//        println("\n\nsub = "+sub.toString)
////        val rez = Huet.applySubToListOfPairs(uprobl, sub)
////        println("\n\nrez after sub = "+rez.toString)
//        println("\n\nrez = "+h.next.get.toString)
//        println("\n\nrez = "+h.next.toString)
////        println("eta <F,ga> = "+Huet.etaBetaNormalization(Tuple2(F,ga)::Nil))
////        Huet.applySubToListOfPairs(Pair(Ffa,Ffa)::Nil, nx) must beEqualTo (Huet.applySubToListOfPairs(Pair(fFa,fFa)::Nil, nx))
//        0 must beEqualTo (0)
//      }


      " return a sub. on <FX,g(F(a))>" in {
        val a = HOLConst(new ConstantStringSymbol("a"), i)
        val F = HOLVar("F", i->i)
        val g = HOLConst(new ConstantStringSymbol("g"), i->i)
        val f = HOLConst(new ConstantStringSymbol("f"), i->i)
        val X = HOLVar("X", i)

        val FX = HOLApp(F,X)

        val gFa = HOLApp(g,Fa)

        val uprobl = Tuple2(FX, gFa)::Nil
        val h = Huet(uprobl)
        val nx = h.next.get
//        println("\n\nsub = "+sub.toString)

        Huet.applySubToListOfPairs(Pair(FX,FX)::Nil, nx) must beEqualTo (Huet.applySubToListOfPairs(Pair(gFa,gFa)::Nil, nx))
      }
    }
}
*/
