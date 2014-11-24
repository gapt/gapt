package at.logic.transformations.ceres.clauseSchema

import at.logic.calculi.slk.SchemaProofDB
import at.logic.language.schema._
import at.logic.language.lambda.types._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import scala.io._

@RunWith(classOf[JUnitRunner])
class resolutionSchemaParserTest extends SpecificationWithJUnit {

  sequential
  "resolutionSchemaParserTest" should {
    "should parse correctly the resolution schema in resSchema1.rs" in {
      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("resSchema1.rs"))
      ParseResSchema(s)
      val k = IntVar("k")
      val map = Map[SchemaVar, SchemaExpression]() + Tuple2(k, Succ(IntZero()))
      val subst = Substitution(map)

      val rho1 = resolutionProofSchemaDB.map.get("\\rho_1").get._2._1
      val rho1step1 = IntVarSubstitution(rho1, subst)

      val z = fo2Var("z")
      val a = SchemaVar("a", Ti)
      val sterm1 = sIndTerm("m", k)//
      val sterm = sTerm("g", sterm1, a::Nil)
      val h = SchemaAbs(k, sterm)
      val mapfo2 = Map[fo2Var, SchemaExpression]() + Tuple2(z.asInstanceOf[fo2Var], h)

      ok
    }

    "should parse correctly the resolution schema in resSchema_sEXP.rs" in {
      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("resSchema_sEXP.rs"))
      ParseResSchema(s)
      val k = IntVar("k")
      val map = Map[SchemaVar, SchemaExpression]() + Tuple2(k, Succ(IntZero()))
      val subst = Substitution(map)

      val rho1 = resolutionProofSchemaDB.map.get("\\rho_1").get._2._1
      val rho1step1 = IntVarSubstitution(rho1, subst)

      ok
    }



    "should parse correctly the resolution schema in resSchema2.rs" in {
      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("resSchema2.rs"))
      ParseResSchema(s)
      val k = IntVar("k")
      val map = Map[SchemaVar, SchemaExpression]() + Tuple2(k, Succ(IntZero()))
      val subst = Substitution(map)
      val rho1 = resolutionProofSchemaDB.map.get("\\rho1").get._2._1
      val rho1step1 = IntVarSubstitution(rho1, subst)

      val z = fo2Var("z")
      val a = SchemaVar("a", Ti)
      val sterm1 = sIndTerm("m", k)//
      val sterm = sTerm("g", sterm1, a::Nil)
      val h = SchemaAbs(k, sterm)
      val mapfo2 = Map[fo2Var, SchemaExpression]() + Tuple2(z.asInstanceOf[fo2Var], h)

      ok
    }

    "should parse correctly the resolution schema in test.rs" in {
      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("test.rs"))
      ParseResSchema(s)

      val k = IntVar("k")
      val map = Map[SchemaVar, SchemaExpression]() + Tuple2(k, Succ(IntZero()))
      val subst = Substitution(map)
      val rho1 = resolutionProofSchemaDB.map.get("\\rho_1").get._2._1
      val rho1step1 = IntVarSubstitution(rho1, subst)

      ok
    }
  }
}

