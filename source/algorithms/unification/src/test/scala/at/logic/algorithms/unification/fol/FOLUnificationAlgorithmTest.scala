/*
 * FOLUnificationAlgorithmTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.unification.fol


import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.algorithms.unification.fol._
import at.logic.language.fol._

private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser

@RunWith(classOf[JUnitRunner])
class FOLUnificationAlgorithmTest extends SpecificationWithJUnit {

  "UnificationBasedFOLMatchingAlgorithm" should {
    "match correctly the lambda expressions f(x1, x2, c) and f(a,b,c)" in {
//     val term = new MyParser("f(x1, x1, x3)").getTerm
//     val posInstance = new MyParser("f(x3,b,g(d))").getTerm
     val term = new MyParser("f(x,x)").getTerm.asInstanceOf[FOLTerm]
     val posInstance = new MyParser("f(a,b)").getTerm.asInstanceOf[FOLTerm]

    // print("\n"+FOLUnificationAlgorithm.applySubToListOfPairs((new MyParser("x").getTerm.asInstanceOf[FOLExpression],new MyParser("a").getTerm.asInstanceOf[FOLExpression])::(new MyParser("x").getTerm.asInstanceOf[FOLExpression],new MyParser("b").getTerm.asInstanceOf[FOLExpression])::Nil,Substitution(new MyParser("x").getTerm.asInstanceOf[FOLVar],new MyParser("c").getTerm.asInstanceOf[FOLExpression])).toString+"\n\n\n")

     val sub = FOLUnificationAlgorithm.unify(term,posInstance)
  //   println("\n\n\n"+sub.toString+"\n\n\n")
  //   sub.get.apply(term) must beEqualTo (posInstance)
    sub must beEqualTo (Nil)
    }
  }

}
