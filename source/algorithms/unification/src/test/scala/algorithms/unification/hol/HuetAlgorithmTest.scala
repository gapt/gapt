/*
 * HuetAlgorithmTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.unification.hol


import algorithms.unification.hol.huet._
import at.logic.language.lambda.BetaReduction
import at.logic.language.lambda.BetaReduction._
import scala.collection.immutable.{Map, HashMap}

import at.logic.language.lambda.substitutions.Substitution
import org.specs._
import org.specs.runner._
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

class HuetAlgorithmTest extends SpecificationWithJUnit with org.specs.ScalaCheck {
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
      val h = HOLConst(new ConstantStringSymbol("h"), i->(i->i))

      val Fa = HOLApp(F,a)
      val Ffa = HOLApp(F,HOLApp(f,a))
      val fFa = HOLApp(f,HOLApp(F,a))
      val gfFafFa = HOLApp(HOLApp(g, fFa), fFa)
      val gFaFa = HOLApp(HOLApp(g, Fa), Fa)
      val gaa = HOLApp(HOLApp(g, a), a)
      val gax = HOLApp(HOLApp(g, a), x)
      val fgaa = HOLApp(f,gaa)
      val fgax = HOLApp(f,gax)
      val ffa = HOLApp(f,fa)



      val fz = HOLApp(f, z)
      val fy = HOLApp(f, y)
      val gfafa = HOLApp(HOLApp(g, fa), fa)
      val gfafx = HOLApp(HOLApp(g, fa), fx)
      val gfbfx = HOLApp(HOLApp(g, fb), fx)

      val f1 = HOLConst(new ConstantStringSymbol("f1"), i->(i->(i->(i->i))))
      val f2 = HOLConst(new ConstantStringSymbol("f2"), (i->(i->i)))


//      val f1xafzy = HOLApp(HOLApp(HOLApp((HOLApp(f, x)), a), fz), y)
//      val f1hayafby = HOLApp(HOLApp(HOLApp(HOLApp(f, HOLApp(HOLApp(h, a), y)), a), fb), y)


      val f2xgay = HOLApp(HOLApp(f2, x), HOLApp(HOLApp(g,a),y))
      val f2xgyx = HOLApp(HOLApp(f2, x), HOLApp(HOLApp(g,y),x))



      val xgax = HOLAbs(x,gax)
      val Fx = HOLApp(F,x)
      val xFx = HOLAbs(x,Fx)
      val H1 = HOLVar("H1", i->i)
      val H2 = HOLVar("H2", i->i)
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

//      "fail on unifying two different constants" in {
//       Huet(c,d).next must beEqual (None    )
//      }

//      "return an empty substitution on two identical constants" in {
//        Huet(c,c).next.get must beEqual (new Substitution[HOLExpression](new HashMap[Var, HOLExpression]()))
//      }
//
//      "return an empty substitution {x->c} on <x,c>" in {
//        Huet(x,c).next.get must beEqual (new Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,c)))
//      }
//
//      "fail on <fa,fb>" in {
//        Huet(fa,fb).next must beEqual (None)
//      }
//
//      "fail on <fa,gaa>" in {
//        Huet(fa,gaa).next must beEqual (None)
//      }
//
//      "fail on <fz, fa>" in {
//        Huet(fz,fa).next.get must beEqual (new Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(z,a)))
//      }
//
//       "fail on <F: i->i, gaa : i> because of different types" in {
//        Huet(F,gaa).next must beEqual (None)
//      }

//
//      "return a subst. {y->fz} on <y, fz>" in {
//        Huet(y,fz).next.get must beEqual (new Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(y,fz)))
//      }
//
//      "return a subst. {x->y} on <x,y>" in {
//        Huet(x,y).next.get must beEqual (new Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,y)))
//      }


//      "return a subst. {x->a} on <fgaa,fgax>" in {
//        Huet(fgax,fgaa).next.get must beEqual (new Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,a)))
//      }

//      "return a subst. {x->a} on <gfafx,gfafa>" in {
//        Huet(gfafx,gfafa).next.get must beEqual (new Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,a)))
//      }

//      "return a subst. {x->a} on <gfafa,gfafx>" in {
//        Huet(gfafa,gfafx).next.get must beEqual (new Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x,a)))
//      }

//      "fail on <gfafa,gfbfx>" in {
//        Huet(gfafa,gfbfx).next must beEqual (None)
//      }

//      "return a sub.  {F:(i->i) -> (λx1:i.f(x3(x1:i):i):i)} on <fFa,ffa>" in {
//        val h = Huet(fFa, ffa)
//        val nx = h.next.get
//        println("\n\nrez = "+nx.toString)
//        println("\n\nrez = "+nx.toString)
//
//         nx must beEqual (new Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(F, HOLAbs(x,HOLApp(f,(HOLApp(f,x))) ))))
//
//      }

//
//      "return a sub.  {F:(i->i) -> (λx1:i.f(x3(x1:i):i):i)} on <fFa,ffa>" in {
//        val h = Huet(f1xafzy, f1hayafby)
//        val nx = h.next.get
//        println("\n\nrez = "+nx.toString)
//        0 must beEqual (0)
////        println("\n\nrez = "+nx.toString)
//
//      }


      "return a sub.  {F:(i->i) -> (λx1:i.f(x3(x1:i):i):i)} on <fFa,ffa>" in {
        val h = Huet(f2xgyx, f2xgay )
        val nx = h.next.get
        println("\n\nrez = "+nx.toString)
        0 must beEqual (0)
        nx must beEqual (new Substitution[HOLExpression](new HashMap[Var, HOLExpression]()+Pair(x, a) + Pair(y, a)))

      }





    }
}
      /*
      "unify flex-flex" in {

      }
    "find all solutions of < , >, < , >"  in {
      import at.logic.parsing.readers.StringReader
      import at.logic.parsing.language.simple._

      class MyParser(input: String) extends StringReader(input) with SimpleHOLParser

      val a = HOLConst(new ConstantStringSymbol("a"), i)
      val b= HOLConst(new ConstantStringSymbol("b"), i)

      val F = HOLVar("F", i->i)
      val y = HOLVar("y", i)
      val z = HOLVar("z", i)
      val f = HOLConst(new ConstantStringSymbol("f"), i->i)
      val fa = HOLApp(f, a)
      val fb= HOLApp(f, b)

      val g = HOLConst(new ConstantStringSymbol("g"), i->(i->i))
      val Fa = HOLApp(F,a)
      val Ffa = HOLApp(F,HOLApp(f,a))
      val fFa = HOLApp(f,HOLApp(F,a))
      val gfFafFa = HOLApp(HOLApp(g, fFa), fFa)
      val gFaFa = HOLApp(HOLApp(g, Fa), Fa)
      val gaa = HOLApp(HOLApp(g, a), a)
      val fz = HOLApp(f, z)
      val fy = HOLApp(f, y)




      val term1a = new MyParser("F(a:i):i").getTerm()
      val term1b = new MyParser("x:i").getTerm()

      val term2a = new MyParser("F(f(a:i):i):i").getTerm()
      val term2b = new MyParser("g(f(x:i):i,f(x:i):i):i").getTerm()


      val x = HOLVar("x", i)
      val H1 = HOLVar("H1", i->i)
      val H2 = HOLVar("H2", i->i)
      val t = Abs(x, App(App(g, App(H1, x)),App(H2,x))).asInstanceOf[HOLExpression]

//      val sigma = Substitution[HOLExpression](F, t)
//      println("\n\nsigma = "+sigma)
//      println("\n\nsigma() = "+sigma(gfFafFa))
//      println("\n\nsigma_beta() = "+BetaReduction.betaNormalize(sigma(gfFafFa))(Outermost))


//      println("\n\nt = "+t.toStringSimple)
//      println("\n\nbeta(t) = "+BetaReduction.betaReduce(t)(Innermost, Leftmost).toStringSimple)

//      (((λ#1:i.g(#3(#1:i):i, #5(#1:i):i):i))(f(a:i):i),g(f(g(#3(a:i):i, #5(a:i):i):i):i, f(((λ#1:i.g(#3(#1:i):i, #5(#1:i):i):i))(a:i)):i):i)
//     (F:(i->i),(λ#1:i.g(#3(#1:i):i, #5(#1:i):i):i)))
//
//      val termb = new MyParser("g(f(F(a:i):i):i,f(F(a:i):i):i):i").getTerm()
//      println("\n\n<"+term2a.toStringSimple+" , "+termb.toStringSimple+">\n\n")


//      val st = HuetAlgorithm.unify1(term2a, termb)
      //val st = HuetAlgorithm.unify1(Ffa, gfFafFa)
//      val st = HuetAlgorithm.unify1(new MyParser("x(f(a:i):i):i").getTerm(),new MyParser("f(x(a:i):i):i").getTerm())
//      val st = HuetAlgorithm.unify1(Ffa, gfFafFa)
//      val st = HuetAlgorithm.unify1(Fa, gFaFa)
//      val st = HuetAlgorithm.unify1(Fa, gaa)
//      val st = HuetAlgorithm.unify1(fy, fz)
//        val st = HuetAlgorithm.unify1(y, fz)
//      val st = HuetAlgorithm.unify1(a,b)
      val st = HuetAlgorithm.unify1(fa,fb)
      println("\n\nThe next unifier is : "+st.next.get.toString)
//      println("\n\nnext : "+st.next.get.toString)
//      println("\n\nnext : "+st.next.get.toString)
//      println("\n\nnext : "+st.next.get.toString)
      println("\n\n")

      0 must beEqual(0)

    }
    "match correctly the lambda expressions f(x1, x2, c) and f(a,b,c)" in {
      val c1 = HOLConst(new ConstantStringSymbol("a"), i->o)
      val v1 = HOLVar("x", i)
      val a1 = App(c1,v1)
      val c2 = HOLVar("a", i->(i->o))
      val v21 = HOLVar("x", i)
      val v22 = HOLVar("y", i)
      val a21 = App(c2,v21)
      val a22 = App(a21,v22)

      val a = HOLConst(new ConstantStringSymbol("a"), i)
      val f = HOLConst(new ConstantStringSymbol("f"), i->i)
      val F = HOLVar("F", i->i)
      val G = HOLVar("G", i->(i->i))
      val g = HOLConst(new ConstantStringSymbol("g"), i->(i->i))

      val G1 = HOLVar("G1", (it.next.get->i)->i)
      val g1 = HOLConst(new ConstantStringSymbol("g1"),(i->i)->i)


      val x = HOLVar("x", i)
      val y = HOLVar("y", i)
      val z = HOLVar("z", i)
      val fx = HOLApp(f,x)
      val Fx = HOLApp(F,x)

    //  val fFa = HOLApp(f,Fa)
      //val Ffa = HOLApp(F,fa)
      val lxfx = HOLAbs(x,fx)
      val lxFx = HOLAbs(x,Fx)
      val Ffx = HOLApp(F,fx)
      val fFx = HOLApp(f,Fx)
      val lyFfx = HOLAbs(y,HOLApp(F,fx))
      val lyfFx = HOLAbs(y,HOLApp(f,Fx))
      val lzlyFfx = HOLAbs(y,HOLAHuetAlgorithm.unify("c","c")pp(F,fx))
      val lzlyfFx = HOLAbs(y,HOLApp(f,Fx))

      val lzlygzy = HOLAbs(z, HOLAbs(y, App(App(g, z), y)))
      val lzlyGzy = HOLAbs(z, HOLAbs(y, App(App(G, z), y)))

      val g1fx = HOLApp(g1, f)
      val G1fx = HOLApp(G1, F)


      val f2 = HOLConst(new ConstantStringSymbol("f2"),i->(i->i))
      val g2 = HOLConst(new ConstantStringSymbol("g2"),(i->(i->i))->i)
      val G2 = HOLVar("G2",(i->(i->i))->i)
      val g2f2 = HOLApp(g2,f2)
      val G2f2 = HOLApp(G2,f2)


      // print("\n"+FOLUnificationAlgorithm.applySubToListOfPairs((new MyParser("x").getTerm.asInstanceOf[FOLExpression],new MyParser("a").getTerm.asInstanceOf[FOLExpression])::(new MyParser("x").getTerm.asInstanceOf[FOLExpression],new MyParser("b").getTerm.asInstanceOf[FOLExpression])::Nil,Substitution(new MyParser("x").getTerm.asInstanceOf[FOLVar],new MyParser("c").getTerm.asInstanceOf[FOLExpression])).toString+"\n\n\n")

  //     val sub = HuetAlgorithm.unify(fFa,Ffa)
  //  //   println("\n\n\n"+sub.toString+"\n\n\n")
  //    sub must beEqual (Nil)




      val sub = HuetAlgorithm.unify(lxFx, lxfx)
      val sub = HuetAlgorithm.unify(lyFfx, lyfFx)
      val sub = HuetAlgorithm.unify(lzlyGzy, lzlygzy)
      val sub = HuetAlgorithm.unify(G1fx, g1fx)
      val sub = HuetAlgorithm.unify(G2f2, g2f2)
      val sub = HuetAlgorithm.unify("c","c")
      val sub = HuetAlgorithm.unify("x", "x")
      val sub = HuetAlgorithm.unify("x", "y")
      val sub = HuetAlgorithm.unify("x", "c")
      val sub = HuetAlgorithm.unify("x", "x")
      val sub = HuetAlgorithm.unify("fx", "fc")
      val sub = HuetAlgorithm.unify("fx", "fy")
      val sub = HuetAlgorithm.unify("ffa", "fxf")
      val sub = HuetAlgorithm.unify("fgaa", "fgax")
      val sub = HuetAlgorithm.unify("y", "fx")
      val sub = HuetAlgorithm.unify("f(f(a),f(x,y,z))", "fx")
      val sub = HuetAlgorithm.unify("f(x,a,g(z),y)", "f(h(a,y),a,g(b),y)")
      val sub = HuetAlgorithm.unify("fgx", "fy")
      val sub = HuetAlgorithm.unify("f(g(x),x)", "f(y,a)")
      val sub = HuetAlgorithm.unify("f(y,g(z),y)", "f(h(a,y),g(b),y)")









//      println("\n\n\n"+sub.toString+"\n\n\n")

//      val st = HuetAlgorithm.unify1(Ffx, fFx)
//      println("\n\n"+st.next.get.toString + " ; "+ st.next.get.toString)
//      println("\n\n")
//      val st = HuetAlgorithm.unify1(fFx, Ffx)
//      println("\n\n"+st.next.get.toString + " ; "+ st.next.get.toString)
//      println("\n\n")

//      prefixes(List(1, 2, 3))

      {
        val Fa = HOLApp(F,a)
        val fa = HOLApp(f,a)
        val fx = HOLApp(f,x)
        val Ffa = HOLApp(F,fa)
        val gfxfx = HOLApp(HOLApp(g, fx), fx)

//        implicit val disAllowedVars = Set[Var]()
//        val st = new NDStream(new ConfigurationNode((Fa, x)::(Ffa, gfxfx)::Nil , Nil), myFun1) with BFSAlgorithm
//        return st
      }


      0 must beEqual(0)


    }
  }
}
*/