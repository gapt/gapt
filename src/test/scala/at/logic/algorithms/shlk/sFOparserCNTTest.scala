/*
* sFOParserCNTTest.scala
*
*/

package at.logic.parsing.shlk_parsing

import at.logic.algorithms.lk.{getCutAncestors, getAncestors}
import at.logic.calculi.lk._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.slk.{TermEquivalenceRule1, TermRightEquivalenceRule1}
import at.logic.language.lambda.types._
import at.logic.language.schema._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.junit.runner.RunWith
import org.specs2.execute.Success
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import scala.io._


@RunWith(classOf[JUnitRunner])
class sFOparserCNTTest extends SpecificationWithJUnit {
  "sFOparserCNT" should {

    sequential
    "parse correctly David's proof " in {
      skipped("has eigenvariable condition errors")

      val A0 = IndexedPredicate("A", IntZero())
      val i = IntVar("i")
      val k = IntVar("k")
      val Ai2 = IndexedPredicate("A", Succ(Succ(i)))
      val Ai = IndexedPredicate("A", Succ(i))
      val f1 = at.logic.language.schema.And(A0, BigAnd(i,Ai,IntZero(),Succ(i)))
      val ax11 = Axiom(A0::Nil, A0::Nil)

      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("David.lks"))

      val map = sFOParserCNT.parseProof(s)

      val p1 = map.get("\\mu").get._2.get("root").get
      val p2 = map.get("\\rho").get._2.get("root").get
      val p3 = map.get("\\zeta").get._2.get("root").get
      val p4 = map.get("\\omega").get._2.get("root").get
      val p5 = map.get("\\xi").get._2.get("root").get
      val p6 = map.get("\\varphi").get._2.get("root").get

      val cc2:FormulaOccurrence = p2.root.antecedent.tail.tail.head
      val cc_zeta_1:FormulaOccurrence = p3.root.succedent.head
      val cc_zeta_2:FormulaOccurrence = p3.root.antecedent.tail.tail.head
      val cc4:FormulaOccurrence = p4.root.succedent.head
      val cc_xi_1:FormulaOccurrence = p5.root.antecedent.last
      val cc_xi_2:FormulaOccurrence = p5.root.succedent.head
      val cc_xi_3:FormulaOccurrence = p5.root.antecedent.tail.head
      val cc6 = p6.root.antecedent.tail.head :: p6.root.antecedent.last ::Nil

      Success()

    }
  }
}


