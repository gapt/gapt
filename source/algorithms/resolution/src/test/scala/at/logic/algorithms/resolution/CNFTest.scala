package at.logic.algorithms.resolution

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

import at.logic.language.fol.{And, Or, Neg, FOLFormula, Atom, FOLConst}
import at.logic.calculi.resolution.FClause

@RunWith(classOf[JUnitRunner])
class CNFTest extends SpecificationWithJUnit {
  "the computation of CNFp(f)" should {
    "be {|- Pa,Qa, Qa|-} for f = (Pa ∨ Qa) ∧ ¬Qa" in {
      val Pa = Atom("P", FOLConst("a")::Nil)
      val Qa = Atom("Q", FOLConst("a")::Nil)
      val nQa = Neg(Qa)
      val PavQa = Or(Pa,Qa)
      val f = And(PavQa, nQa)
      CNFp(f) must beEqualTo(Set(FClause(List(),List(Pa,Qa)),FClause(List(Qa),List())))
    }
  }
}
