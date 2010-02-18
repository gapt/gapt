/*
 * FOLMatchingAlgorithmTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.matching.fol

import org.specs._
import org.specs.runner._
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.algorithms.unification.fol._
import at.logic.language.fol.substitutions._
import at.logic.language.fol._
import at.logic.language.lambda.symbols._

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol
import at.logic.language.hol.propositions.{Neg => HOLNeg, Or => HOLOr, And => HOLAnd, Imp => HOLImp}
import at.logic.language.hol.propositions.{HOL, Formula, HOLVar, HOLConst, HOLApp, HOLAbs, HOLConstFormula, HOLFactory, HOLAppFormula}
import at.logic.language.hol.quantifiers.{AllQ => HOLAllQ, ExQ => HOLExQ}
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types.ImplicitConverters._

import at.logic.language.lambda.symbols._
//import logicSymbols._

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._



//private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser


class FOLMatchingAlgorithmTest extends SpecificationWithJUnit {
  "UnificationBasedFOLMatchingAlgorithm" should {
    "match correctly the lambda expressions f(x, x) and f(a,b)" in {
//     val term = new MyParser("f(x1, x1, x3)").getTerm
//     val posInstance = new MyParser("f(x3,b,g(d))").getTerm
    // val c = FOLVar(ConstantStringSymbol("x"))
//     val term = FOLVar(VariableStringSymbol("x"))
//     val posInstance = FOLConst(ConstantStringSymbol("a"))

       val term = new MyParser("f(x,x)").getTerm
       val posInstance = new MyParser("f(a,b)").getTerm

    // print("\n"+FOLUnificationAlgorithm.applySubToListOfPairs((new MyParser("x").getTerm.asInstanceOf[FOLExpression],new MyParser("a").getTerm.asInstanceOf[FOLExpression])::(new MyParser("x").getTerm.asInstanceOf[FOLExpression],new MyParser("b").getTerm.asInstanceOf[FOLExpression])::Nil,Substitution(new MyParser("x").getTerm.asInstanceOf[FOLVar],new MyParser("c").getTerm.asInstanceOf[FOLExpression])).toString+"\n\n\n")

     val sub = FOLMatchingAlgorithm.matchTerm(term,posInstance)
   //  println("\n\n\n"+"sub: "+sub.toString+"\n\n\n")
  //   sub.get.apply(term) must beEqual (posInstance)
    sub must beEqual (sub)
    }

     
    "match correctly the lambda expressions f(x1, x2, c) and f(a,b,c)" in {
     val term = new MyParser("f(x1, x2, c)").getTerm
     val posInstance = new MyParser("f(a,b,c)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term,posInstance)
//     println("\n\n\nsub : "+sub.toString+"\n\n\n")
     sub.get.apply(term) must beEqual (posInstance)
    }
  

 "not match the lambda expressions f(x1, d, c) and f(a,b,c)" in {
     val term = new MyParser("f(x1, d, c)").getTerm
     val posInstance = new MyParser("f(a,b,c)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term,posInstance)
   //  println("\n\n\nsub : "+sub.toString+"\n\n\n")
     sub must beEqual (None)
    }

  "match the lambda expressions f(x1, x2, c) and f(x1,b,c)" in {
     val term = new MyParser("f(x1, x2, c)").getTerm
     val posInstance = new MyParser("f(x1,b,c)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term,posInstance)
 //    println(sub.toString)
     sub.get.apply(term) must beEqual (posInstance)
    }

  "not match the lambda expressions f(x1, x2, c, d) and f(x1,b,c)" in {
     val term = new MyParser("f(x1, x2, c, d)").getTerm
     val posInstance = new MyParser("f(x1,b,c)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term,posInstance)
     sub must beEqual (None)
    }

  "match the lambda expressions f(x1, x2, c) and f(x3,b,c)" in {
     val term = new MyParser("f(x1, x2, c)").getTerm
     val posInstance = new MyParser("f(x3,b,c)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term,posInstance)
   //  println(sub.toString)
     sub.get.apply(term) must beEqual (posInstance)
    }

  "match the lambda expressions f(x1, x2, x3) and f(x3,b,x3)" in {
     val term = new MyParser("f(x1, x2, x3)").getTerm
     val posInstance = new MyParser("f(x3,b,x3)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term,posInstance)
  //   println(sub.toString)
     sub.get.apply(term) must beEqual (posInstance)
    }

   "match the lambda expressions f(x1, x1, x3) and f(x3,b,g(d))" in {

     val term = new MyParser("f(x1, x1, x3)").getTerm
     val posInstance = new MyParser("f(x3,b,g(d))").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term,posInstance)
   //  println("\n\n\nmatch = "+sub.toString)
     //val sub1 = FOLUnificationAlgorithm.unify(term, posInstance)
  //   println("Printing the substitution "+sub1)
     sub must beEqual (None)
    // println(sub.toString)
    // sub.get.apply(term) must beEqual (posInstance)
    }

  }
}


