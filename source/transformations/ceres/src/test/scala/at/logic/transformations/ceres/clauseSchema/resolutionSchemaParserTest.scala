package at.logic.transformations.ceres.clauseSchema

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import java.io.{FileInputStream, InputStreamReader}
import at.logic.calculi.slk.SchemaProofDB
import java.io.File.separator
import scala.io._

@RunWith(classOf[JUnitRunner])
class resolutionSchemaParserTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory
  import at.logic.language.schema._
  "resolutionSchemaParserTest" should {
    "should parse correctly the resolution schema in resSchema1.rs" in {
      println(Console.BLUE+"\n\n\n\n------- Resolution schema for the resSchema1.rs ------- \n\n"+Console.RESET)
      val s = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema1.rs"))
      ParseResSchema(s)
      println("\ndbTRS:\n"+dbTRS.map)
      println("\n\ndbTRSresolutionSchema:\n"+dbTRSresolutionSchema.map)
//      val rez2 = unfoldingAtomsInResTerm(step, trsSigma, subst)

      println("\n\n")

      println("\n\n--- END ---\n\n")
      ok
    }
  }
}