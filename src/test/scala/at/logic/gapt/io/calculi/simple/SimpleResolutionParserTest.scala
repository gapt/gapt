/*
 * SimpleResolutionParserTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.io.calculi.simple

import at.logic.gapt.proofs.lk.base.FSequent
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.gapt.language.hol._
import at.logic.gapt.language.fol.{FOLVar, FOLConst, FOLAtom => FOLAtom, FOLFunction => FOLFunction}
import at.logic.gapt.io.readers.StringReader
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.resolution.robinson._
import at.logic.gapt.language.lambda.symbols.StringSymbol
import at.logic.gapt.language.lambda.types._

@RunWith(classOf[JUnitRunner])
class SimpleResolutionParserTest extends SpecificationWithJUnit {
//  private class MyParser(input: String) extends StringReader(input) with SimpleResolutionParserHOL
  private class MyParser2(input: String) extends StringReader(input) with SimpleResolutionParserFOL

  val pa = HOLAtom(HOLConst(StringSymbol("p"), Ti -> To),HOLConst(StringSymbol("a"), Ti)::Nil)
  val pfx = HOLAtom(HOLConst(StringSymbol("p"), Ti->To),HOLFunction(HOLConst(StringSymbol("f"), Ti -> Ti), HOLVar(StringSymbol("x"), Ti)::Nil)::Nil)
  val px = HOLAtom(HOLConst(StringSymbol("p"), Ti->To), HOLVar(StringSymbol("x"), Ti)::Nil)
  val pffa = HOLAtom(HOLConst(StringSymbol("p"), Ti -> To),HOLFunction(HOLConst(StringSymbol("f"),Ti->Ti),HOLFunction(HOLConst(StringSymbol("f"), Ti->Ti), HOLConst(StringSymbol("a"), Ti)::Nil)::Nil)::Nil)

  val pa_fol = FOLAtom(StringSymbol("P"),FOLConst(StringSymbol("a"))::Nil)
  val pfx_fol = FOLAtom(StringSymbol("P"),FOLFunction("f", FOLVar(StringSymbol("x"))::Nil)::Nil)
  val px_fol = FOLAtom(StringSymbol("P"),FOLVar(StringSymbol("x"))::Nil)
  val pffa_fol = FOLAtom(StringSymbol("P"),FOLFunction("f",FOLFunction("f", FOLConst("a")::Nil)::Nil)::Nil)

  def clause_to_lists(cl : Clause) : (Seq[Formula], Seq[Formula]) = (cl.negative map (_.formula), cl.positive map (_.formula))


  "SimpleResolutionParser" should {
    /*
    "return an empty clause when given ." in {
      (new MyParser(".").getClauseList) must beEqualTo (Clause(Nil,Nil)::Nil)
    }
    "return an empty list when given nothing" in {
      (new MyParser("").getClauseList) must beEqualTo (Nil)
    }
    "return the correct clause of p(a)." in {
      (new MyParser("p(a:i).").getClauseList) must beEqualTo (Clause(Nil,pa::Nil)::Nil)
    }
    "return the correct clause of p(f(x))." in {
      (new MyParser("p(f(x:i):i).").getClauseList) must beEqualTo (Clause(Nil,pfx::Nil)::Nil)
    }
    "return the correct clause of -p(x)." in {
      (new MyParser("-p(x:i).").getClauseList) must beEqualTo (Clause(px::Nil,Nil)::Nil)
    }
    "return the correct clause of -p(x) | p(f(x))" in {
      (new MyParser("-p(x:i) | p(f(x:i):i).").getClauseList) must beEqualTo (Clause(px::Nil,pfx::Nil)::Nil)
    }
    "return the correct clauses for p(a). -p(x) | p(f(x)). -p(f(f(a)))." in {
      (new MyParser("p(a:i). -p(x:i) | p(f(x:i):i). -p(f(f(a:i):i):i).").getClauseList) must beEqualTo (Clause(Nil,pa::Nil)::Clause(px::Nil,pfx::Nil)::Clause(pffa::Nil,Nil)::Nil)
    }
    */
    "return an empty clause when given ." in {
      (new MyParser2(".").getClauseList) must beEqualTo (Seq(FSequent(Nil,Nil)))
    }
    "return an empty list when given nothing" in {
      (new MyParser2("").getClauseList) must beEqualTo (Nil)
    }
    "return the correct clause of -p(x). fol" in {
      (new MyParser2("-P(x).").getClauseList) must beEqualTo (Seq(FSequent(px_fol::Nil,Nil)))
    }
    "return the correct clauses for p(a). -p(x) | p(f(x)). -p(f(f(a))). in fol" in {
      (new MyParser2("P(a). -P(x) | P(f(x)). -P(f(f(a))).").getClauseList) must beEqualTo (Seq( FSequent(Nil,pa_fol::Nil), FSequent(px_fol::Nil,pfx_fol::Nil), FSequent(pffa_fol::Nil,Nil)))
    }
    /*
    "return the correct clause for p(x) | -p(x) in hol" in {
      (new MyParser("p(x:i) | -p(x:i).").getClauseList) must beEqualTo (Clause(px::Nil,px::Nil)::Nil)
    }*/
    "return the correct clause for p(x) | -p(x) in fol" in {
      (new MyParser2("P(x) | -P(x).").getClauseList) must beEqualTo (Seq(FSequent(px_fol::Nil,px_fol::Nil)))
    }

    /*
    "manage to parse a complex term" in {
      val str = """p(x_10:i,m(x_3:i,m(m(p(x_4:i,one:i):i,p(x_5:i,one:i):i):i):i):i):i"""
      (new MyParser("e("+str+","+str+").").getClauseList) mustNot throwA [Exception]
    }*/
  }
}

