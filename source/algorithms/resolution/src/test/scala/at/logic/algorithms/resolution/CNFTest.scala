package at.logic.algorithms.resolution

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.language.fol.{And, Or, Neg, FOLFormula}
import at.logic.calculi.resolution.base.FClause

@RunWith(classOf[JUnitRunner])
class CNFTest extends SpecificationWithJUnit {
  private class MyParser(str: String) extends StringReader(str) with SimpleFOLParser
  "the computation of CNFp(f)" should {
    "be {|- Pa,Qa, Qa|-} for f = (Pa ∨ Qa) ∧ ¬Qa" in {
      val Pa = new MyParser("P(a)").getTerm.asInstanceOf[FOLFormula]
      val Qa = new MyParser("Q(a)").getTerm.asInstanceOf[FOLFormula]
      val nQa = Neg(Qa)
      val PavQa = Or(Pa,Qa)
      val f = And(PavQa, nQa)
      CNFp(f) must beEqualTo(Set(FClause(List(),List(Pa,Qa)),FClause(List(Qa),List())))
    }
  }
}