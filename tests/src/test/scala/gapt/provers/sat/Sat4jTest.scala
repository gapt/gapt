package gapt.provers.sat

import gapt.examples.{ BussTautology, PigeonHolePrinciple }
import gapt.expr._
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

  "bug 652" in { Sat4j.getDrupProof( fos":- a <-> (a <-> true)" ) must beSome }

  "proof import" in {
    "pigeonhole 4 3" in { Sat4j getResolutionProof PigeonHolePrinciple( 4, 3 ) must beSome }
    "buss 5" in { Sat4j getResolutionProof BussTautology( 5 ) must beSome }
    "to be or not to be" in { Sat4j getResolutionProof hof"be ∨ ¬be" must beSome }
  }
}
