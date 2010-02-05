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

private class MyParser(input: String) extends StringReader(input) with SimpleResolutionParserFOL
private object MyAlg extends StillmanSubsumptionAlgorithm {val matchAlg = NaiveIncompleteMatchingAlgorithm} // incomplete matching algorithm

class StillmanSubsumptionAlgorithmTest extends SpecificationWithJUnit {
  "StillmanSubsumptionAlgorithm" should {
    "return true on the following clauses" in {
      "P(x) | P(f(x,y)) and P(a) | P(b) | P(f(b,a))" in {
        MyAlg.subsumes(new MyParser("P(x) | P(f(x,y)).").getClauseList.head.positive, new MyParser("P(a) | P(b) | P(f(b,a)).").getClauseList.head.positive) must beEqual (true)
      }
      "Nil and P(a) | P(b) | P(f(b,a))" in {
        MyAlg.subsumes(Nil, new MyParser("P(a) | P(b) | P(f(b,a)).").getClauseList.head.positive) must beEqual (true)
      }
      "P(x) and P(x) | P(f(x,y))" in {
        MyAlg.subsumes(new MyParser("P(x).").getClauseList.head.positive, new MyParser("P(x) | P(f(x,y)).").getClauseList.head.positive) must beEqual (true)
      }
      "P(x) and P(x)" in {
        MyAlg.subsumes(new MyParser("P(x).").getClauseList.head.positive, new MyParser("P(x).").getClauseList.head.positive) must beEqual (true)
      }
      "P(x) and P(y)" in {
        MyAlg.subsumes(new MyParser("P(x).").getClauseList.head.positive, new MyParser("P(y).").getClauseList.head.positive) must beEqual (true)
      }
      "P(x,x) | P(x,a) and P(a,a)" in {
        MyAlg.subsumes(new MyParser("P(x,x) | P(x,a).").getClauseList.head.positive, new MyParser("P(a,a).").getClauseList.head.positive) must beEqual (true)
      }
    }
    "return false on the following clauses" in {
      "P(x) | P(f(x)) and P(f(a)) | P(f(b))" in {
        MyAlg.subsumes(new MyParser("P(x) | P(f(x)).").getClauseList.head.positive, new MyParser("P(f(a)) | P(f(b)).").getClauseList.head.positive) must beEqual (false)
      }
      "P(a,a) and P(x,x) | P(x,a)" in {
        MyAlg.subsumes(new MyParser("P(a,a).").getClauseList.head.positive, new MyParser("P(x,x) | P(x,a).").getClauseList.head.positive) must beEqual (false)
      }
      "P(x,x) | P(x,b) and P(b,a) | P(a,b)" in {
        MyAlg.subsumes(new MyParser("P(x,x) | P(x,b).").getClauseList.head.positive, new MyParser("P(b,a) | P(a,b).").getClauseList.head.positive) must beEqual (false)
      }
    }
  }
}
