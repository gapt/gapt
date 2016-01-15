package at.logic.gapt.provers.sat

import at.logic.gapt.expr._
import org.specs2.mutable._

class Sat4jTest extends Specification {
  "find a model for an atom" in { Sat4j.solve( SATProblems.getProblem1() ) must beSome }

  "see that Pc and -Pc is unsat" in { Sat4j.solve( SATProblems.getProblem2() ) must beNone }

  "see that Pc or -Pc is valid" in {
    Sat4j.isValid( SATProblems.getProblem3a() ) must beTrue
    Sat4j.isValid( SATProblems.getProblem3b() ) must beTrue
  }

  "see that Pc is not valid" in {
    Sat4j.isValid( SATProblems.getProblem4() ) must beFalse
  }

  "return a correct model" in {
    Sat4j.solve( SATProblems.getProblem5() ) must beLike {
      case Some( model ) => SATProblems.checkSolution5( model ) must beTrue
    }
  }

  "deal correctly with the pigeonhole problem" in {
    SATProblems.getProblem6a() foreach { f => Sat4j.isValid( f ) must beFalse }
    SATProblems.getProblem6b() foreach { f => Sat4j.isValid( f ) must beTrue }
    ok
  }

  "say bottom is unsatisfiable" in { Sat4j.solve( Bottom() ) must beNone }
  "say top is satisfiable" in { Sat4j.solve( Top() ) must beSome }

  "empty CNF is sat" in { Sat4j.solve( Seq() ) must beSome }
  "empty clause is unsat" in { Sat4j.solve( Seq( Seq() ) ) must beNone }
}
