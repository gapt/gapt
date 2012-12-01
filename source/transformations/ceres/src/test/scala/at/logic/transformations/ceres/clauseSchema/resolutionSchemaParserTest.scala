//package at.logic.transformations.ceres.clauseSchema
//
//import org.junit.runner.RunWith
//import org.specs2.runner.JUnitRunner
//import org.specs2.mutable.SpecificationWithJUnit
//import at.logic.language.lambda.symbols.VariableStringSymbol
//import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
//import java.io.{FileInputStream, InputStreamReader}
//import at.logic.calculi.slk.SchemaProofDB
//import java.io.File.separator
//import scala.io._
//import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
//import at.logic.language.hol.HOLAbs._
//import at.logic.language.hol.HOLVar._
//import at.logic.language.lambda.types.Ti._
//import at.logic.language.lambda.types.Ti
//import at.logic.language.schema.sTerm._
//import at.logic.algorithms.shlk._
//import at.logic.calculi.lk.base.Sequent
//import at.logic.language.hol.{HOLFormula, HOLVar, HOLAbs, HOLExpression}
//
//@RunWith(classOf[JUnitRunner])
//class resolutionSchemaParserTest extends SpecificationWithJUnit {
//  implicit val factory = defaultFormulaOccurrenceFactory
//  import at.logic.language.schema._
//  "resolutionSchemaParserTest" should {
//    "should parse correctly the resolution schema in resSchema1.rs" in {
//      println(Console.BLUE+"\n\n\n\n------- Resolution schema for the resSchema1.rs ------- \n\n"+Console.RESET)
//      val s = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema1.rs"))
//      ParseResSchema(s)
//      println("\ndbTRS:\n"+dbTRS.map)
//      println("\n\ndbTRSresolutionSchema:\n")
//      resolutionProofSchemaDB.map.foreach(m => println(m))
//      val k = IntVar(new VariableStringSymbol("k"))
//      val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], Succ(IntZero()))
//      val subst = new SchemaSubstitution3(map)
//      val rho1 = resolutionProofSchemaDB.map.get("\\rho_1").get._2._1
//      val rho1step1 = IntVarSubstitution(rho1, subst)
//      println("rho1step1 = "+rho1step1)
//      val r = unfoldResolutionProofSchema2(rho1step1)
//      println("r = "+r)
//
//      val z = fo2Var(new VariableStringSymbol("z"))
//      val a = HOLVar(new VariableStringSymbol("a"), Ti())
////      val h = HOLAbs(k, a)
////      val sterm1 = dbTRS.map.head._2._2._1
//      val sterm1 = sIndTerm("m", k)//
//      val sterm = sTerm("g", sterm1, a::Nil)
//      val h = HOLAbs(k, sterm)
//      val mapfo2 = Map[fo2Var, LambdaExpression]() + Pair(z.asInstanceOf[fo2Var], h)
//      val fo2sub = fo2VarSubstitution(r, mapfo2).asInstanceOf[sResolutionTerm]
//      println(Console.BOLD+"applying second-order substitution:\n\n"+Console.RESET)
//      println("fo2sub = "+fo2sub)
//
//      println("\n\nresolution deduction tree:")
//      printSchemaProof(ResDeductionToLKTree(fo2sub))
//      println("\n\n--- END ---\n\n")
//      ok
//    }
//
//    "should parse correctly the resolution schema in resSchema2.rs" in {
//      println(Console.RED+"\n\n\n\n------- Resolution schema for the resSchema2.rs ------- \n\n"+Console.RESET)
//      val s = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema2.rs"))
//      ParseResSchema(s)
////      println("\ndbTRS:\n"+dbTRS.map)
//      println("\n\ndbTRSresolutionSchema:\n")
//      resolutionProofSchemaDB.map.foreach(m => println(m+"\n"))
//      println("\n")
//      val k = IntVar(new VariableStringSymbol("k"))
//      val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], Succ(IntZero()))
//      val subst = new SchemaSubstitution3(map)
//      val rho1 = resolutionProofSchemaDB.map.get("\\rho1").get._2._1
//      val rho1step1 = IntVarSubstitution(rho1, subst)
//      println("rho1step1 = "+rho1step1)
//      val r = unfoldResolutionProofSchema2(rho1step1)
//      println("r = "+r)
//
//      val z = fo2Var(new VariableStringSymbol("z"))
//      val a = HOLVar(new VariableStringSymbol("a"), Ti())
//      //      val h = HOLAbs(k, a)
//      //      val sterm1 = dbTRS.map.head._2._2._1
//      val sterm1 = sIndTerm("m", k)//
//      val sterm = sTerm("g", sterm1, a::Nil)
//      val h = HOLAbs(k, sterm)
//      val mapfo2 = Map[fo2Var, LambdaExpression]() + Pair(z.asInstanceOf[fo2Var], h)
//      val fo2sub = fo2VarSubstitution(r, mapfo2).asInstanceOf[sResolutionTerm]
//      println(Console.BOLD+"applying second-order substitution:\n\n"+Console.RESET)
//      println("fo2sub = "+fo2sub)
////
////      println("\n\nresolution deduction tree:")
////      printSchemaProof(ResDeductionToLKTree(fo2sub))
////      InstantiateResSchema("\\rho1",2)
//      println("\n\n--- END ---\n\n")
//      ok
//    }
//  }
//}
//
