package at.logic.gapt.provers.sat

import at.logic.gapt.expr._
import org.specs2.mutable._

class MiniSATTest extends Specification {
  if ( !MiniSAT.isInstalled ) skipAll

  "find a model for an atom" in { MiniSAT.solve( SATProblems.getProblem1() ) must beSome }

  "see that Pc and -Pc is unsat" in { MiniSAT.solve( SATProblems.getProblem2() ) must beNone }

  "see that Pc or -Pc is valid" in {
    MiniSAT.isValid( SATProblems.getProblem3a() ) must beTrue
    MiniSAT.isValid( SATProblems.getProblem3b() ) must beTrue
  }

  "see that Pc is not valid" in {
    MiniSAT.isValid( SATProblems.getProblem4() ) must beFalse
  }

  "return a correct model" in {
    MiniSAT.solve( SATProblems.getProblem5() ) must beLike {
      case Some( model ) => SATProblems.checkSolution5( model ) must beTrue
    }
  }

  "deal correctly with the pigeonhole problem" in {
    SATProblems.getProblem6a() foreach { f => MiniSAT.isValid( f ) must beFalse }
    SATProblems.getProblem6b() foreach { f => MiniSAT.isValid( f ) must beTrue }
    ok
  }

  "say bottom is unsatisfiable" in { MiniSAT.solve( Bottom() ) must beNone }
  "say top is satisfiable" in { MiniSAT.solve( Top() ) must beSome }

  "empty CNF is sat" in { MiniSAT.solve( Seq() ) must beSome }
  "empty clause is unsat" in { MiniSAT.solve( Seq( Seq() ) ) must beNone }
}
