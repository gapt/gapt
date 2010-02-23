/*
 * MatchingAlgorithmTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.matching.fol

import org.specs._
import org.specs.runner._
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleFOLParser

import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm

private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser

/*class UnificationBasedFOLMatchingAlgorithmTest extends SpecificationWithJUnit {

  "UnificationBasedFOLMatchingAlgorithm " should {
    "match correctly the lambda expressions f(x1, x2, c) and f(a,b,c)" in {
     val term = new MyParser("f(x1, x2, c)").getTerm
     val posInstance = new MyParser("f(a,b,c)").getTerm
     val sub = UnificationBasedFOLMatchingAlgorithm.matchTerm(term,posInstance)
 //    println(sub.toString)
     sub.get.apply(term) must beEqual (posInstance)
    }
  }

 "not match the lambda expressions f(x1, d, c) and f(a,b,c)" in {
     val term = new MyParser("f(x1, d, c)").getTerm
     val posInstance = new MyParser("f(a,b,c)").getTerm
     val sub = UnificationBasedFOLMatchingAlgorithm.matchTerm(term,posInstance)
     sub must beEqual (None)
    }

  "match the lambda expressions f(x1, x2, c) and f(x1,b,c)" in {
     val term = new MyParser("f(x1, x2, c)").getTerm
     val posInstance = new MyParser("f(x1,b,c)").getTerm
     val sub = UnificationBasedFOLMatchingAlgorithm.matchTerm(term,posInstance)
 //    println(sub.toString)
     sub.get.apply(term) must beEqual (posInstance)
    }

  "not match the lambda expressions f(x1, x2, c, d) and f(x1,b,c)" in {
     val term = new MyParser("f(x1, x2, c, d)").getTerm
     val posInstance = new MyParser("f(x1,b,c)").getTerm
     val sub = UnificationBasedFOLMatchingAlgorithm.matchTerm(term,posInstance)
     sub must beEqual (None)
    }

  "match the lambda expressions f(x1, x2, c) and f(x3,b,c)" in {
     val term = new MyParser("f(x1, x2, c)").getTerm
     val posInstance = new MyParser("f(x3,b,c)").getTerm
     val sub = UnificationBasedFOLMatchingAlgorithm.matchTerm(term,posInstance)
   //  println(sub.toString)
     sub.get.apply(term) must beEqual (posInstance)
    }

  "match the lambda expressions f(x1, x2, x3) and f(x3,b,x3)" in {
     val term = new MyParser("f(x1, x2, x3)").getTerm
     val posInstance = new MyParser("f(x3,b,x3)").getTerm
     val sub = UnificationBasedFOLMatchingAlgorithm.matchTerm(term,posInstance)
  //   println(sub.toString)
     sub.get.apply(term) must beEqual (posInstance)
    }

   "match the lambda expressions f(x1, x1, x3) and f(x3,b,g(d))" in {
 
     val term = new MyParser("f(x1, x1, x3)").getTerm
     val posInstance = new MyParser("f(x3,b,g(d))").getTerm
     val sub = UnificationBasedFOLMatchingAlgorithm.matchTerm(term,posInstance)
  //   println("\n\n\nmatch = "+sub.toString)
     val sub1 = FOLUnificationAlgorithm.unify(term, posInstance)
  //   println("Printing the substitution "+sub1)
     sub must beEqual (None)
    // println(sub.toString)
    // sub.get.apply(term) must beEqual (posInstance)
    }
  }
  




  

*/