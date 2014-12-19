package at.logic.algorithms.resolution

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.language.hol.{Atom => HOLAtom, HOLConst}
import at.logic.language.lambda.types.To
import at.logic.language.fol.{And, Or, Neg, Atom, FOLConst, Imp}
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

  "the computation of TseitinCNF(f)" should {
    "should be right, where f = ((P ∨ Q) ∧ R ) -> ¬S" in {
      val p = Atom("P", Nil)
      val q = Atom("Q", Nil)
      val r = Atom("R", Nil)
      val s = Atom("S", Nil)

      val f = Imp(And(Or(p, q), r), Neg(s))

      val x =  Atom("x", Nil)
      val x0 = Atom("x0", Nil)
      val x1 = Atom("x1", Nil)
      val x2 = Atom("x2", Nil)

      val cnf = TseitinCNF(f)
      val expected = Set(
        FClause(List(), List(x2)),
        FClause(List(x1), List(x2)),
        FClause(List(), List(x2, x0)),
        FClause(List(), List(x1, s)),
        FClause(List(x1, s), List()),
        FClause(List(x0), List(r)),
        FClause(List(x0), List(x)),
        FClause(List(q), List(x)),
        FClause(List(p), List(x)),
        FClause(List(x2, x0), List(x1)),
        FClause(List(x, r), List(x0)),
        FClause(List(x), List(p, q))
      )
      cnf._1 must beEqualTo(expected)
    }
  }
}
