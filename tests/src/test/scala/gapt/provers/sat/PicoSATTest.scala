package gapt.provers.sat

import gapt.examples.{ BussTautology, PigeonHolePrinciple }
import gapt.expr._
import org.specs2.mutable._

class PicoSATTest extends Specification {
  if ( !PicoSAT.isInstalled ) skipAll

  "find a model for an atom" in { PicoSAT.solve( SATProblems.getProblem1() ) must beSome }

  "see that Pc and -Pc is unsat" in { PicoSAT.solve( SATProblems.getProblem2() ) must beNone }

  "see that Pc or -Pc is valid" in {
    PicoSAT.isValid( SATProblems.getProblem3a() ) must beTrue
    PicoSAT.isValid( SATProblems.getProblem3b() ) must beTrue
  }

  "see that Pc is not valid" in {
    PicoSAT.isValid( SATProblems.getProblem4() ) must beFalse
  }

  "return a correct model" in {
    PicoSAT.solve( SATProblems.getProblem5() ) must beLike {
      case Some( model ) => SATProblems.checkSolution5( model ) must beTrue
    }
  }

  "deal correctly with the pigeonhole problem" in {
    SATProblems.getProblem6a() foreach { f => PicoSAT.isValid( f ) must beFalse }
    SATProblems.getProblem6b() foreach { f => PicoSAT.isValid( f ) must beTrue }
    ok
  }

  "say bottom is unsatisfiable" in { PicoSAT.solve( Bottom() ) must beNone }
  "say top is satisfiable" in { PicoSAT.solve( Top() ) must beSome }

  "empty CNF is sat" in { PicoSAT.solve( Seq() ) must beSome }
  "empty clause is unsat" in { PicoSAT.solve( Seq( Seq() ) ) must beNone }

  "proof import" in {
    "pigeonhole 3 2" in { PicoSAT getResolutionProof PigeonHolePrinciple( 3, 2 ) must beSome }
    "buss 5" in { PicoSAT getResolutionProof BussTautology( 5 ) must beSome }
    "to be or not to be" in { PicoSAT getResolutionProof hof"be ∨ ¬be" must beSome }
  }
}
