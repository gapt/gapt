package at.logic.algorithms.hlk

import at.logic.language.schema._
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules.OrLeftRule
import at.logic.calculi.lk.propositionalRules.NegLeftRule
import at.logic.calculi.lk.propositionalRules.Axiom
import at.logic.calculi.lk.propositionalRules.{OrLeftRule, NegLeftRule, Axiom}
import at.logic.calculi.lksk.Axiom
import at.logic.parsing.readers.StringReader
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol._
import at.logic.language.hol.Definitions._
import at.logic.language.hol.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.parsing.readers.StringReader
import scala.io._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.specs2.execute.Success
import at.logic.parsing.readers.StringReader
import at.logic.language.hol.HOLVarFormula
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.schema.IndexedPredicate
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.schema.IntZero
import at.logic.language.schema.IntVar
import at.logic.language.schema.Succ
import at.logic.language.schema.BigAnd
import at.logic.language.hol.HOLConst
import at.logic.language.lambda.types.Ti
import at.logic.language.lambda.types.->
import at.logic.language.lambda.types.Tindex
import at.logic.language.schema.foVar
import at.logic.language.schema.foTerm
import at.logic.language.schema.sTerm
import at.logic.language.schema.dbTRS

@RunWith(classOf[JUnitRunner])
class LKParserTest extends SpecificationWithJUnit {
  private class MyParser extends StringReader("")
  "LKParser" should {

    "parse correctly a FO LK-proof" in {
      println(Console.BLUE+"\n---- START ----\n"+Console.RESET)
      val s = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "proof1.lk"))
      val map = LKProofParser.parseProof(s)

      println("\n\nend_seq = "+  map.get("\\psi").get._1.get("root").get.root.toString()  )
      println(Console.BLUE+"\n--------\n"+Console.RESET)
      Success()
    }


    " parse a fol proof of all n all x all y. x+y = " in {



      Success()
    }
  }
}


