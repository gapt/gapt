/*
 * StillmanSubsumptionAlgorithmTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption

import org.specs._
import org.specs.runner._
import at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
import at.logic.parsing.readers.StringReader
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.calculi.simple.SimpleResolutionParserHOL

private class MyParser(input: String) extends StringReader(input) with SimpleResolutionParserFOL
private class MyParserHOL(input: String) extends StringReader(input) with SimpleResolutionParserHOL
private object MyAlg extends StillmanSubsumptionAlgorithm {val matchAlg = NaiveIncompleteMatchingAlgorithm} // incomplete matching algorithm

class StillmanSubsumptionAlgorithmTest extends SpecificationWithJUnit {
  "StillmanSubsumptionAlgorithm" should {
    "return true on the following clauses" in {
      "P(x) | P(f(x,y)) and P(a) | P(b) | P(f(b,a))" in {
        MyAlg.subsumes((Nil, new MyParser("P(x) | P(f(x,y)).").getClauseList.head.positive), (Nil, new MyParser("P(a) | P(b) | P(f(b,a)).").getClauseList.head.positive)) must beEqual (true)
      }
      "Nil and P(a) | P(b) | P(f(b,a))" in {
        MyAlg.subsumes((Nil, Nil), (Nil, new MyParser("P(a) | P(b) | P(f(b,a)).").getClauseList.head.positive)) must beEqual (true)
      }
      "P(x) and P(x) | P(f(x,y))" in {
        MyAlg.subsumes((Nil, new MyParser("P(x).").getClauseList.head.positive), (Nil, new MyParser("P(x) | P(f(x,y)).").getClauseList.head.positive)) must beEqual (true)
      }
      "P(x) and P(x)" in {
        MyAlg.subsumes((Nil, new MyParser("P(x).").getClauseList.head.positive), (Nil, new MyParser("P(x).").getClauseList.head.positive)) must beEqual (true)
      }
      "P(x) and P(y)" in {
        MyAlg.subsumes((Nil, new MyParser("P(x).").getClauseList.head.positive),(Nil,  new MyParser("P(y).").getClauseList.head.positive)) must beEqual (true)
      }
      "P(x,x) | P(x,a) and P(a,a)" in {
        MyAlg.subsumes((Nil, new MyParser("P(x,x) | P(x,a).").getClauseList.head.positive), (Nil, new MyParser("P(a,a).").getClauseList.head.positive)) must beEqual (true)
      }
      "P(x:i,x:i) | P(x:i,a:i) and P(a:i,a:i)" in {
        MyAlg.subsumes((Nil, new MyParserHOL("P(x:i,x:i) | P(x:i,a:i).").getClauseList.head.positive), (Nil, new MyParserHOL("P(a:i,a:i).").getClauseList.head.positive)) must beEqual (true)
      }
      "P(x:i,x:i) and P(f(y:i,z:i,a:i):i,f(y:i,z:i,a:i):i)" in {
        MyAlg.subsumes((Nil, new MyParserHOL("P(x:i,x:i).").getClauseList.head.positive), (Nil, new MyParserHOL("P(f(y:i,z:i,a:i):i,f(y:i,z:i,a:i):i).").getClauseList.head.positive)) must beEqual (true)
      }
      "P(x:i,x:i) and P(f(q:(i->o),z:i,a:i):i,f(q:(i->o),z:i,a:i):i) | -Q(f(b:i):(i->i))" in {
        val cl2 = new MyParserHOL("P(f(q:(i->o),z:i,a:i):i,f(q:(i->o),z:i,a:i):i) | -Q(f(b:i):(i->i)).").getClauseList.head
        MyAlg.subsumes((Nil, new MyParserHOL("P(x:i,x:i).").getClauseList.head.positive), (cl2.negative, cl2.positive)) must beEqual (true)
      }
      //val str = """+(s50(q1:(i->o)):i, *(s43(q1: (i->o), +(*(+(x3:i, 1):i, s49(q1:(i->o), s50(q1:(i->o)):i):i):i, x3:i):i):i, *(+(x3, 1):i, +(s49(q1:(i->o), s50(q1:(i->o)):i), 1:i):i):i):i):i"""
      val str = """p(x_10:i,m(x_3:i,m(m(p(x_4:i,one:i):i,p(x_5:i,one:i):i):i):i):i):i"""
      "e(x,x):i and e("+str+","+str+"):i" in {
        MyAlg.subsumes((Nil, new MyParserHOL("e(x:i,x:i).").getClauseList.head.positive), (Nil, new MyParserHOL("e("+str+","+str+").").getClauseList.head.positive)) must beEqual (true)
      }
      "P(x:i) and P(a:i) | Q(x:i)" in {
        MyAlg.subsumes((Nil, new MyParserHOL("P(x:i).").getClauseList.head.positive), (Nil, new MyParserHOL("P(a:i) | Q(x:i).").getClauseList.head.positive)) must beEqual (true)
      }
    }
    "return false on the following clauses" in {
      "P(x) | P(f(x)) and P(f(a)) | P(f(b))" in {
        MyAlg.subsumes((Nil, new MyParser("P(x) | P(f(x)).").getClauseList.head.positive), (Nil, new MyParser("P(f(a)) | P(f(b)).").getClauseList.head.positive)) must beEqual (false)
      }
      "P(a,a) and P(x,x) | P(x,a)" in {
        MyAlg.subsumes((Nil, new MyParser("P(a,a).").getClauseList.head.positive), (Nil, new MyParser("P(x,x) | P(x,a).").getClauseList.head.positive)) must beEqual (false)
      }
      "P(x,x) | P(x,b) and P(b,a) | P(a,b)" in {
        MyAlg.subsumes((Nil, new MyParser("P(x,x) | P(x,b).").getClauseList.head.positive), (Nil, new MyParser("P(b,a) | P(a,b).").getClauseList.head.positive)) must beEqual (false)
      }
      "P(x) | -P(x) and P(a) | -P(b)" in {
        val cl1 = new MyParser("P(x) | -P(x).").getClauseList.head
        val cl2 = new MyParser("P(a) | -P(b).").getClauseList.head
        MyAlg.subsumes((cl1.negative, cl1.positive), (cl2.negative, cl2.positive)) must beEqual (false)
      }
      "P(x) | -P(x) and P(y) | -P(z)" in {
        val cl1 = new MyParser("P(x) | -P(x).").getClauseList.head
        val cl2 = new MyParser("P(y) | -P(z).").getClauseList.head
        MyAlg.subsumes((cl1.negative, cl1.positive), (cl2.negative, cl2.positive)) must beEqual (false)
      }
    }
  }
}
