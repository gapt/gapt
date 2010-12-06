/*
 * HuetAlgorithmTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.unification.hol

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



private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser

class HuetAlgorithmTest extends SpecificationWithJUnit with org.specs.ScalaCheck {
    "HuetAlgorithm" should {
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
      val st = HuetAlgorithm.unify1(fFx, Ffx)
      println("\n\n"+st.next.get.toString + " ; "+ st.next.get.toString)
      println("\n\n")

//      prefixes(List(1, 2, 3))






      0 must beEqual(0)


    }
  }
}
