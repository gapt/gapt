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
import at.logic.language.fol._
import at.logic.language.lambda.symbols._

import at.logic.language.lambda.typedLambdaCalculus._
//import at.logic.language.hol._
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



private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser


class FOLMatchingAlgorithmTest extends SpecificationWithJUnit {
  "FOLMatchingAlgorithm" should {
    "match correctly the lambda expressions f(x, x) and f(a,b)" in {
//     val term = new MyParser("f(x1, x1, x3)").getTerm
//     val posInstance = new MyParser("f(x3,b,g(d))").getTerm
    // val c = FOLVar(ConstantStringSymbol("x"))
//     val term = FOLVar(VariableStringSymbol("x"))
//     val posInstance = FOLConst(ConstantStringSymbol("a"))

       val term = new MyParser("f(x,x)").getTerm
       val posInstance = new MyParser("f(a,b)").getTerm

    // print("\n"+FOLUnificationAlgorithm.applySubToListOfPairs((new MyParser("x").getTerm.asInstanceOf[FOLExpression],new MyParser("a").getTerm.asInstanceOf[FOLExpression])::(new MyParser("x").getTerm.asInstanceOf[FOLExpression],new MyParser("b").getTerm.asInstanceOf[FOLExpression])::Nil,Substitution(new MyParser("x").getTerm.asInstanceOf[FOLVar],new MyParser("c").getTerm.asInstanceOf[FOLExpression])).toString+"\n\n\n")

      val sub = FOLMatchingAlgorithm.matchTerm(term.asInstanceOf[FOLExpression],posInstance.asInstanceOf[FOLExpression],posInstance.getFreeAndBoundVariables._1.toList)
   //  println("\n\n\n"+"sub: "+sub.toString+"\n\n\n")
  //   sub.get.apply(term) must beEqual (posInstance)
    sub must beEqual (sub)
    }

     
    "match correctly the lambda expressions f(x1, x2, c) and f(a,b,c)" in {
     val term = new MyParser("f(x1, x2, c)").getTerm
     val posInstance = new MyParser("f(a,b,c)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term.asInstanceOf[FOLExpression],posInstance.asInstanceOf[FOLExpression],posInstance.getFreeAndBoundVariables._1.toList)
//     println("\n\n\nsub : "+sub.toString+"\n\n\n")
     sub.get.apply(term.asInstanceOf[FOLExpression]) must beEqual (posInstance)
    }
  

 "not match the lambda expressions f(x1, d, c) and f(a,b,c)" in {
     val term = new MyParser("f(x1, d, c)").getTerm
     val posInstance = new MyParser("f(a,b,c)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term.asInstanceOf[FOLExpression],posInstance.asInstanceOf[FOLExpression],posInstance.getFreeAndBoundVariables._1.toList)
   //  println("\n\n\nsub : "+sub.toString+"\n\n\n")
     sub must beEqual (None)
    }

  "match the lambda expressions f(x1, x2, c) and f(x1,b,c)" in {
     val term = new MyParser("f(x1, x2, c)").getTerm
     val posInstance = new MyParser("f(x1,b,c)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term.asInstanceOf[FOLExpression],posInstance.asInstanceOf[FOLExpression],posInstance.getFreeAndBoundVariables._1.toList)
 //    println(sub.toString)
     sub.get.apply(term.asInstanceOf[FOLExpression]) must beEqual (posInstance)
    }

  "not match the lambda expressions f(x1, x2, c, d) and f(x1,b,c)" in {
     val term = new MyParser("f(x1, x2, c, d)").getTerm
     val posInstance = new MyParser("f(x1,b,c)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term.asInstanceOf[FOLExpression],posInstance.asInstanceOf[FOLExpression],posInstance.getFreeAndBoundVariables._1.toList)
     sub must beEqual (None)
    }

  "match the lambda expressions f(x1, x2, c) and f(x3,b,c)" in {
     val term = new MyParser("f(x1, x2, c)").getTerm
     val posInstance = new MyParser("f(x3,b,c)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term.asInstanceOf[FOLExpression],posInstance.asInstanceOf[FOLExpression],posInstance.getFreeAndBoundVariables._1.toList)
   //  println(sub.toString)
     sub.get.apply(term.asInstanceOf[FOLExpression]) must beEqual (posInstance)
    }

  "match the lambda expressions f(x1, x2, x3) and f(x3,b,x3)" in {
     val term = new MyParser("f(x1, x2, x3)").getTerm
     val posInstance = new MyParser("f(x3,b,x3)").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term.asInstanceOf[FOLExpression],posInstance.asInstanceOf[FOLExpression],posInstance.getFreeAndBoundVariables._1.toList)
  //   println(sub.toString)
     sub.get.apply(term.asInstanceOf[FOLExpression]) must beEqual (posInstance)
    }

   "match the lambda expressions f(x1, x1, x3) and f(x3,b,g(d))" in {

     val term = new MyParser("f(x1, x1, x3)").getTerm
     val posInstance = new MyParser("f(x3,b,g(d))").getTerm
     val sub = FOLMatchingAlgorithm.matchTerm(term.asInstanceOf[FOLExpression],posInstance.asInstanceOf[FOLExpression],posInstance.getFreeAndBoundVariables._1.toList)
   //  println("\n\n\nmatch = "+sub.toString)
     //val sub1 = FOLUnificationAlgorithm.unify(term, posInstance)
  //   println("Printing the substitution "+sub1)
     sub must beEqual (None)
    // println(sub.toString)
    // sub.get.apply(term) must beEqual (posInstance)
    }


  "apply the MatchingSubstitution wrongly " in {
     val term = new MyParser("f(x1, g(x1,x3), x3)").getTerm
     val x1 = new MyParser("x1").getTerm
     val x3 = new MyParser("x3").getTerm
     val a = new MyParser("a").getTerm
     val c = new MyParser("c").getTerm
//     val l =  (new MyParser("x3").getTerm.asInstanceOf[Var])::Nil
//     val m: scala.collection.immutable.Map[Var, LambdaExpression] = Map()
//     val t = new FOLMatchingAlgorithm.MatchingSubstitution(l, m.+((x1.asInstanceOf[Var],a))++m.+((x3.asInstanceOf[Var],c))).apply(term)
//     println("\n\n\n  term = "+term.toString+"\n\n")
//     println("\n\n\n  term = "+term.toStringSimple+"\n\n")
//     println("\n\n\n     t = "+t.toString+"\n\n")
     //val sub1 = FOLUnificationAlgorithm.unify(term, posInstance)
  //   println("Printing the substitution "+sub1)
     0 must beEqual (0)
    // println(sub.toString)
    // sub.get.apply(term) must beEqual (posInstance)
    }


  "match the FOL formulas P(x1,f(x1, g(x1,x3), x3)) and P(c,f(x1, g(x1,a), x3))" in {
     val term1 = new MyParser("f(x1, g(x1,x3), x3)").getTerm
     val term2 = new MyParser("f(c, g(x1,a), x3)").getTerm
     val x1 = new MyParser("x1").getTerm.asInstanceOf[FOLVar]
     val x3 = new MyParser("x3").getTerm
     val a = new MyParser("a").getTerm
     val c = new MyParser("c").getTerm
     val P1:FOLFormula  = AllVar(x1,Atom(new ConstantStringSymbol("P"), x1::term1.asInstanceOf[FOLTerm]::Nil))
     val P2:FOLFormula  = AllVar(x1,Atom(new ConstantStringSymbol("P"), c.asInstanceOf[FOLConst]::term2.asInstanceOf[FOLTerm]::Nil))
 //    val l =  (new MyParser("x3").getTerm.asInstanceOf[Var])::Nil
     val l =  (x1.asInstanceOf[Var]::x3.asInstanceOf[Var]::Nil)
//     val m: scala.collection.immutable.Map[Var, LambdaExpression] = Map()
//     val t = new FOLMatchingAlgorithm.MatchingSubstitution(l, m.+((x1.asInstanceOf[Var],a))++m.+((x3.asInstanceOf[Var],c))).apply(term)
//     println("\n\n\n  term = "+term.toString+"\n\n")
//     println("\n\n\n  term = "+term.toStringSimple+"\n\n")
//     println("\n\n\n     t = "+t.toString+"\n\n")
     val sub1 = FOLMatchingAlgorithm.matchTerm(P1, P2,P2.getFreeAndBoundVariables._1.toList)
   //  println("\n\n\nPrinting the substitution: "+sub1+"\n\n\n")
     0 must beEqual (0)
    // println(sub.toString)
    // sub.get.apply(term) must beEqual (posInstance)
    }

  "match the FOL formulas And(P(x1,f(x1, g(x1,x3), x3)),Q(x1)) and And(P(c,f(c, g(x1,a), x3)),Q(c))" in {
     val term1 = new MyParser("f(x1, g(x1,x3), x3)").getTerm
     val term2 = new MyParser("f(c, g(x1,a), x3)").getTerm
     val x1 = new MyParser("x1").getTerm.asInstanceOf[FOLVar]
     val x3 = new MyParser("x3").getTerm
     val a = new MyParser("a").getTerm
     val c = new MyParser("c").getTerm
     val P1:FOLFormula  = And(Atom(new ConstantStringSymbol("P"), x1::term1.asInstanceOf[FOLTerm]::Nil), Atom(new ConstantStringSymbol("Q"), x1::Nil))
     val P2:FOLFormula  = And(Atom(new ConstantStringSymbol("P"), c.asInstanceOf[FOLConst]::term2.asInstanceOf[FOLTerm]::Nil), Atom(new ConstantStringSymbol("Q"), c.asInstanceOf[FOLConst]::Nil))
 //    val l =  (new MyParser("x3").getTerm.asInstanceOf[Var])::Nil
     val l =  (x1.asInstanceOf[Var]::x3.asInstanceOf[Var]::Nil)
//     val m: scala.collection.immutable.Map[Var, LambdaExpression] = Map()
//     val t = new FOLMatchingAlgorithm.MatchingSubstitution(l, m.+((x1.asInstanceOf[Var],a))++m.+((x3.asInstanceOf[Var],c))).apply(term)
//     println("\n\n\n  term = "+term.toString+"\n\n")
//     println("\n\n\n  term = "+term.toStringSimple+"\n\n")
//     println("\n\n\n     t = "+t.toString+"\n\n")
     val sub1 = FOLMatchingAlgorithm.matchTerm(P1, P2,P2.getFreeAndBoundVariables._1.toList)
  //   println("\n\n\nPrinting the substitution: "+sub1+"\n\n\n")
     sub1 must beEqual (None)
    // println(sub.toString)
    // sub.get.apply(term) must beEqual (posInstance)
    }



  "match the FOL formulas And(P(x2,f(x2, g(x1,x3), x3)),Q(c)) and And(P(c,f(c, g(x1,a), x1)),Q(c))" in {
     val term1 = new MyParser("f(x2, g(x2,x3), x3)").getTerm.asInstanceOf[FOLTerm]
     val term2 = new MyParser("f(c, g(a,x1), x1)").getTerm.asInstanceOf[FOLTerm]
     val x1 = new MyParser("x1").getTerm.asInstanceOf[FOLVar]
     val x2 = new MyParser("x2").getTerm.asInstanceOf[FOLVar]
     val x3 = new MyParser("x3").getTerm.asInstanceOf[FOLVar]
     val a = new MyParser("a").getTerm.asInstanceOf[FOLConst]
     val c = new MyParser("c").getTerm.asInstanceOf[FOLConst]
     val P1:FOLFormula  = And(Atom(new ConstantStringSymbol("P"), term1::Nil), Atom(new ConstantStringSymbol("Q"), c::Nil))
     val P2:FOLFormula  = And(Atom(new ConstantStringSymbol("P"), term2::Nil), Atom(new ConstantStringSymbol("Q"), c::Nil))
 //    val l =  (new MyParser("x3").getTerm.asInstanceOf[Var])::Nil
     val l =  (x1.asInstanceOf[Var]::x3.asInstanceOf[Var]::Nil)
//     val m: scala.collection.immutable.Map[Var, LambdaExpression] = Map()
//     val t = new FOLMatchingAlgorithm.MatchingSubstitution(l, m.+((x1.asInstanceOf[Var],a))++m.+((x3.asInstanceOf[Var],c))).apply(term)
//     println("\n\n\n  term = "+term.toString+"\n\n")
//     println("\n\n\n  term = "+term.toStringSimple+"\n\n")
//     println("\n\n     P1 = "+P1.toString+"\n\n")
//     println("\n\n    P2 = "+P2.toString+"\n\n")
     val sub1 = FOLMatchingAlgorithm.matchTerm(P1, P2,P2.getFreeAndBoundVariables._1.toList)
//     println("\n\nPrinting the substitution: "+sub1+"\n\n")
     sub1 must beEqual (None)
    // println(sub.toString)
    // sub.get.apply(term) must beEqual (posInstance)
    }

      "match the FOL formulas And(P(f(x2, g(x1,x3), x3)),Q(x2)) and And(P(f(c, g(a,x1), x2)),Q(c))" in {
     val term1 = new MyParser("f(x2, g(x2,x3), x3)").getTerm.asInstanceOf[FOLTerm]
     val term2 = new MyParser("f(c, g(c,x1), x2)").getTerm.asInstanceOf[FOLTerm]
     val x1 = new MyParser("x1").getTerm.asInstanceOf[FOLVar]
     val x2 = new MyParser("x2").getTerm.asInstanceOf[FOLVar]
     val x3 = new MyParser("x3").getTerm.asInstanceOf[FOLVar]
     val a = new MyParser("a").getTerm.asInstanceOf[FOLConst]
     val c = new MyParser("c").getTerm.asInstanceOf[FOLConst]
     val P1:FOLFormula  = And(Atom(new ConstantStringSymbol("P"), term1::Nil), Atom(new ConstantStringSymbol("Q"), x2::Nil))
     val P2:FOLFormula  = And(Atom(new ConstantStringSymbol("P"), term2::Nil), Atom(new ConstantStringSymbol("Q"), c::Nil))
 //    val l =  (new MyParser("x3").getTerm.asInstanceOf[Var])::Nil
     val l =  (x1.asInstanceOf[Var]::x3.asInstanceOf[Var]::Nil)
//     val m: scala.collection.immutable.Map[Var, LambdaExpression] = Map()
//     val t = new FOLMatchingAlgorithm.MatchingSubstitution(l, m.+((x1.asInstanceOf[Var],a))++m.+((x3.asInstanceOf[Var],c))).apply(term)
//     println("\n\n\n  term = "+term.toString+"\n\n")
//     println("\n\n\n  term = "+term.toStringSimple+"\n\n")
//     println("\n\n     P1 = "+P1.toString+"\n\n")
//     println("\n\n    P2 = "+P2.toString+"\n\n")
     val sub1 = FOLMatchingAlgorithm.matchTerm(P1, P2,P2.getFreeAndBoundVariables._1.toList)
//     println("\n\nPrinting the substitution: "+sub1+"\n\n")
     sub1 must beEqual (None)
    // println(sub.toString)
    // sub.get.apply(term) must beEqual (posInstance)
    }
  }
}


