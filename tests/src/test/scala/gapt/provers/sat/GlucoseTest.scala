package gapt.provers.sat

import gapt.examples.{BussTautology, PigeonHolePrinciple}
import gapt.expr._
import gapt.expr.formula.Bottom
import gapt.expr.formula.Top
import org.specs2.mutable._

class GlucoseTest extends Specification {
  if (!Glucose.isInstalled) skipAll

  "find a model for an atom" in { Glucose.solve(SATProblems.getProblem1()) must beSome }

  "see that Pc and -Pc is unsat" in { Glucose.solve(SATProblems.getProblem2()) must beNone }

  "see that Pc or -Pc is valid" in {
    Glucose.isValid(SATProblems.getProblem3a()) must beTrue
    Glucose.isValid(SATProblems.getProblem3b()) must beTrue
  }

  "see that Pc is not valid" in {
    Glucose.isValid(SATProblems.getProblem4()) must beFalse
  }

  "return a correct model" in {
    Glucose.solve(SATProblems.getProblem5()) must beLike {
      case Some(model) => SATProblems.checkSolution5(model) must beTrue
    }
  }

  "deal correctly with the pigeonhole problem" in {
    SATProblems.getProblem6a() foreach { f => Glucose.isValid(f) must beFalse }
    SATProblems.getProblem6b() foreach { f => Glucose.isValid(f) must beTrue }
    ok
  }

  "say bottom is unsatisfiable" in { Glucose.solve(Bottom()) must beNone }
  "say top is satisfiable" in { Glucose.solve(Top()) must beSome }

  "empty CNF is sat" in { Glucose.solve(Seq()) must beSome }
  "empty clause is unsat" in { Glucose.solve(Seq(Seq())) must beNone }

  "proof import" in {
    "pigeonhole 3 2" in { Glucose getResolutionProof PigeonHolePrinciple(3, 2) must beSome }
    "buss 5" in { Glucose getResolutionProof BussTautology(5) must beSome }
    "to be or not to be" in { Glucose getResolutionProof hof"be ∨ ¬be" must beSome }
  }
}
