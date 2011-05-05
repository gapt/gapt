/*
 * HuetAlgorithmTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.unification.hol

import at.logic.language.lambda.BetaReduction
import at.logic.language.lambda.BetaReduction._

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
    "find all solutions of <Fa,x>, <Ffa,g(fx,fx)>"  in {
      import at.logic.parsing.readers.StringReader
      import at.logic.parsing.language.simple._

      class MyParser(input: String) extends StringReader(input) with SimpleHOLParser

      val a = HOLConst(new ConstantStringSymbol("a"), i)
      val F = HOLVar("F", i->i)
      val f = HOLConst(new ConstantStringSymbol("f"), i->i)
      val g = HOLConst(new ConstantStringSymbol("g"), i->(i->i))
      val Fa = HOLApp(F,a)
      val Ffa = HOLApp(F,HOLApp(f,a))
      val fFa = HOLApp(f,HOLApp(F,a))
      val gfFafFa = HOLApp(HOLApp(g, fFa), fFa)
      val gFaFa = HOLApp(HOLApp(g, Fa), Fa)
      val gaa = HOLApp(HOLApp(g, a), a)



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
      val st = HuetAlgorithm.unify1(Fa, gaa)
      println("\n\nnext : "+st.next.get.toString)
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

      val G1 = HOLVar("G1", (i->i)->i)
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
      val lzlyFfx = HOLAbs(y,HOLApp(F,fx))
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




//      val sub = HuetAlgorithm.unify(lxFx, lxfx)
//      val sub = HuetAlgorithm.unify(lyFfx, lyfFx)
//      val sub = HuetAlgorithm.unify(lzlyGzy, lzlygzy)
//      val sub = HuetAlgorithm.unify(G1fx, g1fx)
//      val sub = HuetAlgorithm.unify(G2f2, g2f2)
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
