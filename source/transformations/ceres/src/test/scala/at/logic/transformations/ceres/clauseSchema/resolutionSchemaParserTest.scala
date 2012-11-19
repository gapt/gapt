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
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
import at.logic.language.hol.HOLAbs._
import at.logic.language.hol.HOLVar._
import at.logic.language.lambda.types.Ti._
import at.logic.language.lambda.types.Ti
import at.logic.language.hol.{HOLVar, HOLAbs, HOLExpression}

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
      println("\n\ndbTRSresolutionSchema:\n")
      dbTRSresolutionSchema.map.foreach(m => println(m))
      val k = IntVar(new VariableStringSymbol("k"))
      val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], Succ(Succ(IntZero())))
      val subst = new SchemaSubstitution3(map)
      val r = unfoldResolutionProofSchema2(dbTRSresolutionSchema.map.get("ρ1").get._2._1, subst)
      println("\n\n")
      println("r = "+r)
      println("\n\n")
      val z = fo2Var(new VariableStringSymbol("z"))
      val a = HOLVar(new VariableStringSymbol("a"), Ti())
      val h = HOLAbs(k, a)
      val mapfo2 = Map[fo2Var, LambdaExpression]() + Pair(z.asInstanceOf[fo2Var], h)
      val fo2sub = fo2VarSubstitution(r, mapfo2).asInstanceOf[sResolutionTerm]
      println(Console.BOLD+"applying second-order substitution:\n\n"+Console.RESET+fo2sub)



      println("\n\n--- END ---\n\n")
      ok
    }
  }
}