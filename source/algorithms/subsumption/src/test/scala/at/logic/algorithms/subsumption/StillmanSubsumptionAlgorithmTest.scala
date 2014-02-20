/*
 * StillmanSubsumptionAlgorithmTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption

import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm
import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
import at.logic.parsing.readers.StringReader
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
//import at.logic.parsing.calculi.simple.SimpleResolutionParserHOL
import at.logic.calculi.lk.base._
import at.logic.language.fol._
import at.logic.language.hol._
import at.logic.calculi.lk.base.types._

private class MyParser(input: String) extends StringReader(input) with SimpleResolutionParserFOL
//private class MyParserHOL(input: String) extends StringReader(input) with SimpleResolutionParserHOL
private object MyAlg extends StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}
private object MyAlgHOL extends StillmanSubsumptionAlgorithm[HOLExpression] {val matchAlg = NaiveIncompleteMatchingAlgorithm} // incomplete matching algorithm

@RunWith(classOf[JUnitRunner])
class StillmanSubsumptionAlgorithmTest extends SpecificationWithJUnit {
  "StillmanSubsumptionAlgorithm" should {
    "return true on the following clauses" in {
      "P(x) | P(f(x,y)) and P(a) | P(b) | P(f(b,a))" in {
        MyAlg.subsumes(new MyParser("P(x) | P(f(x,y)).").getClauseList.head, new MyParser("P(a) | P(b) | P(f(b,a)).").getClauseList.head) must beEqualTo (true)
      }
      "Nil and P(a) | P(b) | P(f(b,a))" in {
        MyAlg.subsumes(new FSequent(Nil,Nil), new MyParser("P(a) | P(b) | P(f(b,a)).").getClauseList.head) must beEqualTo (true)
      }
      "P(x) and P(x) | P(f(x,y))" in {
        MyAlg.subsumes(new MyParser("P(x).").getClauseList.head, new MyParser("P(x) | P(f(x,y)).").getClauseList.head) must beEqualTo (true)
      }
      "P(x) and P(x)" in {
        MyAlg.subsumes(new MyParser("P(x).").getClauseList.head, new MyParser("P(x).").getClauseList.head) must beEqualTo (true)
      }
      "P(x) and P(y)" in {
        MyAlg.subsumes(new MyParser("P(x).").getClauseList.head,new MyParser("P(y).").getClauseList.head) must beEqualTo (true)
      }
      "P(x,x) | P(x,a) and P(a,a)" in {
        MyAlg.subsumes(new MyParser("P(x,x) | P(x,a).").getClauseList.head, new MyParser("P(a,a).").getClauseList.head) must beEqualTo (true)
      }
      "P(x,y) and P(x,y)" in {
        MyAlg.subsumes(new MyParser("P(x,y).").getClauseList.head, new MyParser("P(x,y).").getClauseList.head) must beEqualTo (true)
      }
      "P(x,y) and P(x1,y1)" in {
        MyAlg.subsumes(new MyParser("P(x,y).").getClauseList.head, new MyParser("P(x1,y1).").getClauseList.head) must beEqualTo (true)
      }

      "P(x,y) and P(y,x)" in {
        MyAlg.subsumes(new MyParser("P(x,y).").getClauseList.head, new MyParser("P(y,x).").getClauseList.head) must beEqualTo (true)
      }

      /*"P(x) | Q(x,y) and P(a) | Q(a,y) | R(x)" in {
        MyAlg.subsumes(new MyParser("P(x) | Q(x,y).").getClauseList.head, new MyParser("P(a) | Q(a,y) | R(x).").getClauseList.head) must beEqualTo (true)
      } */
      /*"P(x:i,x:i) | P(x:i,a:i) and P(a:i,a:i)" in {
        MyAlgHOL.subsumes(new MyParserHOL("P(x:i,x:i) | P(x:i,a:i).").getClauseList.head, new MyParserHOL("P(a:i,a:i).").getClauseList.head) must beEqualTo (true)
      }
      "P(x:i,x:i) and P(f(y:i,z:i,a:i):i,f(y:i,z:i,a:i):i)" in {
        MyAlgHOL.subsumes(new MyParserHOL("P(x:i,x:i).").getClauseList.head, new MyParserHOL("P(f(y:i,z:i,a:i):i,f(y:i,z:i,a:i):i).").getClauseList.head) must beEqualTo (true)
      }
      "P(x:i,x:i) and P(f(q:(i->o),z:i,a:i):i,f(q:(i->o),z:i,a:i):i) | -Q(f(b:i):(i->i))" in {
        val cl2 = new MyParserHOL("P(f(q:(i->o),z:i,a:i):i,f(q:(i->o),z:i,a:i):i) | -Q(f(b:i):(i->i)).").getClauseList.head
        MyAlgHOL.subsumes(new MyParserHOL("P(x:i,x:i).").getClauseList.head, cl2) must beEqualTo (true)
      }
      //val str = """+(s50(q1:(i->o)):i, *(s43(q1: (i->o), +(*(+(x3:i, 1):i, s49(q1:(i->o), s50(q1:(i->o)):i):i):i, x3:i):i):i, *(+(x3, 1):i, +(s49(q1:(i->o), s50(q1:(i->o)):i), 1:i):i):i):i):i"""
      val str = """p(x_10:i,m(x_3:i,m(m(p(x_4:i,one:i):i,p(x_5:i,one:i):i):i):i):i):i"""
      "e(x,x):i and e("+str+","+str+"):i" in {
        MyAlgHOL.subsumes(new MyParserHOL("e(x:i,x:i).").getClauseList.head, new MyParserHOL("e("+str+","+str+").").getClauseList.head) must beEqualTo (true)
      }
      "P(x:i) and P(a:i) | Q(x:i)" in {
        MyAlgHOL.subsumes(new MyParserHOL("P(x:i).").getClauseList.head, new MyParserHOL("P(a:i) | Q(x:i).").getClauseList.head) must beEqualTo (true)
      }*/
    }
    "return false on the following clauses" in {
      "P(x) | P(f(x)) and P(f(a)) | P(f(b))" in {
        MyAlg.subsumes(new MyParser("P(x) | P(f(x)).").getClauseList.head, new MyParser("P(f(a)) | P(f(b)).").getClauseList.head) must beEqualTo (false)
      }
      "P(a,a) and P(x,x) | P(x,a)" in {
        MyAlg.subsumes(new MyParser("P(a,a).").getClauseList.head, new MyParser("P(x,x) | P(x,a).").getClauseList.head) must beEqualTo (false)
      }
      "P(x,x) | P(x,b) and P(b,a) | P(a,b)" in {
        MyAlg.subsumes(new MyParser("P(x,x) | P(x,b).").getClauseList.head, new MyParser("P(b,a) | P(a,b).").getClauseList.head) must beEqualTo (false)
      }
      "P(x) | -P(x) and P(a) | -P(b)" in {
        val cl1 = new MyParser("P(x) | -P(x).").getClauseList.head
        val cl2 = new MyParser("P(a) | -P(b).").getClauseList.head
        MyAlg.subsumes(cl1, cl2) must beEqualTo (false)
      }
      "P(x) | -P(x) and P(y) | -P(z)" in {
        val cl1 = new MyParser("P(x) | -P(x).").getClauseList.head
        val cl2 = new MyParser("P(y) | -P(z).").getClauseList.head
        MyAlg.subsumes(cl1, cl2) must beEqualTo (false)
      }
      /*"P(x) and P(a) | P(y)" in {
        val cl1 = new MyParser("P(x).").getClauseList.head
        val cl2 = new MyParser("P(a) | P(y).").getClauseList.head
        MyAlg.subsumes(cl1, cl2) must beEqualTo (false)
      } */
      "P(x) | -P(x) and P(y) | -P(z)" in {
        val cl1 = new MyParser("P(x) | -P(x).").getClauseList.head
        val cl2 = new MyParser("P(y) | -P(z).").getClauseList.head
        MyAlg.subsumes(cl1, cl2) must beEqualTo (false)
      }
    }
  }
}
