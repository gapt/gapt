/*
 * Tests for the MiniSAT interface.
**/

package at.logic.gapt.provers.sat4j

import java.io.IOException

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.gapt.language.fol._
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.expr.types._
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.models.Interpretation
import at.logic.gapt.provers.minisat.SATProblems

@RunWith( classOf[JUnitRunner] )
class Sat4JTest extends SpecificationWithJUnit {
  "Sat4J" should {
    "find a model for an atom" in {
      ( new Sat4j ).solve( SATProblems.getProblem1() ) must beLike {
        case Some( model ) => ok
        case None          => ko
      }
    }

    "see that Pc and -Pc is unsat" in {
      ( new Sat4j ).solve( SATProblems.getProblem2() ) must beLike {
        case Some( _ ) => ko
        case None      => ok
      }
    }

    "see that Pc or -Pc is valid" in {
      ( new Sat4j ).isValid( SATProblems.getProblem3a() ) must beTrue
      ( new Sat4jProver ).isValid( SATProblems.getProblem3b() ) must beTrue
    }

    "see that Pc is not valid" in {
      ( new Sat4j ).isValid( SATProblems.getProblem4() ) must beFalse
    }

    "return a correct model" in {
      ( new Sat4j ).solve( SATProblems.getProblem5() ) must beLike {
        case Some( model ) => if ( SATProblems.checkSolution5( model ) ) ok else ko
        case None          => ko
      }

    }

    "deal correctly with the pigeonhole problem" in {
      val sol_a = SATProblems.getProblem6a().map( ( new Sat4j ).isValid( _ ) )
      val sol_b = SATProblems.getProblem6b().map( ( new Sat4j ).isValid( _ ) )

      sol_a must_== sol_a.map( x => false )
      sol_b must_== sol_b.map( x => true )
    }

    "say bottom is unsatisfiable" in {
      new Sat4j().solve( FOLBottomC ) must beNone
    }

    "say top is satisfiable" in {
      new Sat4j().solve( FOLTopC ) must beLike {
        case Some( _ ) => ok
        case None      => ko
      }
    }
  }
}
