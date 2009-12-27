/*
 * SimpleResolutionParserTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.calculi.simple

import org.specs._
import org.specs.runner._
import at.logic.language.hol.propositions._
import at.logic.language.hol.quantifiers._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.propositions.Definitions._
import at.logic.language.hol.propositions.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.parsing.readers.StringReader
import at.logic.calculi.resolution.base._
import at.logic.language.hol.propositions.Definitions._
import at.logic.language.hol.propositions.ImplicitConverters._

class SimpleResolutionParserTest extends SpecificationWithJUnit {
  private class MyParser(input: String) extends StringReader(input) with SimpleResolutionParser
  "SimpleResolutionParser" should {
    "return an empty clause when given ." in {
      (new MyParser(".").getClauseList) must beEqual (Clause(Nil,Nil)::Nil)
    }
    "return an empty list when given nothing" in {
      (new MyParser("").getClauseList) must beEqual (Nil)
    }
    val pa = Atom(ConstantStringSymbol("p"),Var(ConstantStringSymbol("a"), i, hol)::Nil)
    "return the correct clause of p(a)." in {
      (new MyParser("p(a:i).").getClauseList) must beEqual (Clause(Nil,pa::Nil)::Nil)
    }
    /*val pfa = Atom(ConstantStringSymbol("p"),Function(ConstantStringSymbol("f"), Var(ConstantStringSymbol("a"), i, hol)::Nil,i)::Nil)
    "return the correct clause of p(a)." in {
      (new MyParser("p(f(a:i):i).").getClauseList) must beEqual (Clause(Nil,pfa::Nil)::Nil)
    }*/
  }
}
