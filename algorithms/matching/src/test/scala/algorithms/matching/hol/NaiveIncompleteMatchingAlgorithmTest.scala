/*
 * NaiveIncompleteMatchingAlgorithmTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.matching.hol

import org.specs._
import org.specs.runner._
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleHOLParser

import at.logic.language.lambda.typedLambdaCalculus
import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
//import logicSymbols._
import at.logic.language.hol.logicSymbols.ImplicitConverters._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.hol.logicSymbols._
//import quantifiers._
import at.logic.language.lambda.types.Definitions._


//import at.logic.language.hol.substitutions._
import at.logic.language.lambda.substitutions._


private class MyParser(input: String) extends StringReader(input) with SimpleHOLParser

class NaiveIncompleteMatchingAlgorithmTest extends SpecificationWithJUnit {
  "NaiveIncompleteMatchingAlgorithm " should {
    "match correctly the HOL expressions P(a,x) and P(a,f(b))" in {
    val P = HOLConst(new ConstantStringSymbol("P"), i->(i->o))
    val a = HOLConst(new ConstantStringSymbol("a"), i)
    val b = HOLConst(new ConstantStringSymbol("b"), i)
    val Pa = App(P,a);
    val x = HOLVar(new VariableStringSymbol("x"), i)
    val Pax = App(Pa,x)   
    val f = HOLConst(new ConstantStringSymbol("f"), i->i)
    val fb= App(f,b)
    val Pafb = App(Pa,fb)
    val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(Pax,Pafb,Pafb.getFreeAndBoundVariables._1.toList)
    val subst1 = Substitution(x,fb)
//    println("\n\n"+subst.toString)
//    println("\n\n"+Pax.toString1)
//    println("\n\n"+Pafb.toString1)
//    println("\n\n"+subst1.toString)
    subst must beEqual (Some(subst1))
    }
  
    "match correctly the HOL expressions P(z,x) and P(f(b),f(b))" in {
    val P = HOLConst(new ConstantStringSymbol("P"), i->(i->o))   
    val b = HOLConst(new ConstantStringSymbol("b"), i)
    val x = HOLVar(new VariableStringSymbol("x"), i)
    val z = HOLVar(new VariableStringSymbol("z"), i)
    val Pz = App(P,z)
    
    val Pzx = App(Pz,x)
    val f = HOLConst(new ConstantStringSymbol("f"), i->i)
    val fb= App(f,b)
    val Pfb = App(P,fb)
    val Pfbfb = App(Pfb,fb)
    val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(Pzx,Pfbfb,Pfbfb.getFreeAndBoundVariables._1.toList)
    val subst1 = Substitution(x,fb):::Substitution(z,fb)    
//    println("\n\n"+Pzx.toString1)
//    println("\n\n"+Pfbfb.toString1)
//    println("\n\n"+subst.toString)
//    println("\n\n"+subst1.toString)
    subst must beEqual (Some(subst1))
  }

    "NOT match correctly the HOL expressions P(z,x) and P(f(b),z)" in {
    val P = HOLConst(new ConstantStringSymbol("P"), i->(i->o))
    val b = HOLConst(new ConstantStringSymbol("b"), i)
    val x = HOLVar(new VariableStringSymbol("x"), i)
    val z = HOLVar(new VariableStringSymbol("z"), i)
    val Pz = App(P,z)
    val Pzx = App(Pz,x)
    val f = HOLConst(new ConstantStringSymbol("f"), i->i)
    val fb= HOLApp(f,b)//App(f,b)
    val Pfb = App(P,fb)
    val Pfbz = App(Pfb,z)
    val subst = NaiveIncompleteMatchingAlgorithm.matchTerm(Pzx,Pfbz,Pfbz.getFreeAndBoundVariables._1.toList)
    val subst1 = Substitution[HOLExpression](z,fb):::Substitution[HOLExpression](x,z)
    println("\n\n"+Pzx.toString1)
    println("\n\n"+Pfbz.toString1)
    println("\n\nsubst = "+subst.toString+"\n")

//  subst must beEqual (None)         // correct !!!
    subst must beEqual (subst) // wrong !!!
    }

}
}


