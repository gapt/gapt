package at.logic.transformations.ceres.ACNF

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import java.io.{FileInputStream, InputStreamReader}
import at.logic.calculi.slk.SchemaProofDB
import java.io.File.separator
import scala.io._
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
import at.logic.language.hol.HOLAbs._
import at.logic.language.hol.HOLVar._
import at.logic.language.lambda.types.Ti._
import at.logic.language.lambda.types.Ti
import at.logic.language.schema.sTerm._
import at.logic.algorithms.shlk._
import at.logic.calculi.lk.base.Sequent
import at.logic.language.hol.{HOLFormula, HOLVar, HOLAbs, HOLExpression}
import at.logic.transformations.ceres.clauseSchema._

@RunWith(classOf[JUnitRunner])
class ACNFTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory
  "ACNFTest" should {
    "should create correctly the ACNF for journal_example.lks" in {
      println(Console.BLUE+"\n\n\n\n------- ACNF for the journal example ------- \n\n"+Console.RESET)
      val s1 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "journal_example.lks"))
      val s2 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema1.rs"))
      val map = sFOParser.parseProof(s1)
      ParseResSchema(s2)
      val p = ACNF("\\varphi", "\\rho_1", 1)
      printSchemaProof(p)
      println("\n\n--- END ---\n\n")
      ok
    }
  }
}

