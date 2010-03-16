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
import at.logic.language.hol.Definitions

import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.hol.Definitions



private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser

class HuetAlgorithmTest extends SpecificationWithJUnit {
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
    
    val fa = App(f,a)
    val Fa = App(F,a)
    val fFa = App(f,Fa)
    val Ffa = App(F,fa)

    // print("\n"+FOLUnificationAlgorithm.applySubToListOfPairs((new MyParser("x").getTerm.asInstanceOf[FOLExpression],new MyParser("a").getTerm.asInstanceOf[FOLExpression])::(new MyParser("x").getTerm.asInstanceOf[FOLExpression],new MyParser("b").getTerm.asInstanceOf[FOLExpression])::Nil,Substitution(new MyParser("x").getTerm.asInstanceOf[FOLVar],new MyParser("c").getTerm.asInstanceOf[FOLExpression])).toString+"\n\n\n")

     val sub = HuetAlgorithm.unify(fFa,Ffa)
  //   println("\n\n\n"+sub.toString+"\n\n\n")  
    sub must beEqual (None)
    }
  }
}
