/*
 * Tests for the MiniSAT interface.
**/

package at.logic.gapt.provers.minisat

import java.io.IOException

import at.logic.gapt.examples.PigeonHolePrinciple
import at.logic.gapt.models.Interpretation
import at.logic.gapt.proofs.{ HOLSequent, HOLClause }
import org.specs2.mutable._

import at.logic.gapt.expr._
import at.logic.gapt.proofs.resolution._

object SATProblems {
  val c = FOLConst( "c" )
  val d = FOLConst( "d" )
  val e = FOLConst( "e" )
  val pc = FOLAtom( "P", c :: Nil )
  val pd = FOLAtom( "P", d :: Nil )
  val pe = FOLAtom( "P", e :: Nil )

  def getProblem1() = HOLClause( Nil, pc :: Nil ) :: Nil
  def getProblem2() = {
    val c1 = HOLClause( Nil, pc :: Nil )
    val c2 = HOLClause( pc :: Nil, Nil )
    c1 :: c2 :: Nil
  }
  def getProblem3a() = Or( pc, Neg( pc ) )
  def getProblem3b() = new HOLSequent( Nil, Or( pc, Neg( pc ) ) :: Nil )
  def getProblem4() = pc
  def getProblem5() = {
    val c1 = HOLClause( Nil, pc :: Nil )
    val c2 = HOLClause( pc :: Nil, pd :: Nil )
    val c3 = HOLClause( pd :: pe :: Nil, Nil )
    c1 :: c2 :: c3 :: Nil
  }
  def checkSolution5( model: Interpretation ) = model.interpret( pe ) == false

  private def problem6( pair: ( Int, Int ) ) = PigeonHolePrinciple( pair._1, pair._2 )

  def getProblem6a(): List[FOLFormula] = {
    val fparams = List( ( 2, 2 ), ( 3, 3 ), ( 4, 4 ) )
    fparams.map( problem6 )
  }

  def getProblem6b(): List[FOLFormula] = {
    val tparams = List( ( 2, 1 ), ( 3, 2 ), ( 4, 3 ), ( 4, 1 ) )
    tparams.map( problem6 )
  }
}

class MiniSATTest extends Specification {
  args( skipAll = !( new MiniSATProver ).isInstalled )

  "MiniSAT" should {
    "find a model for an atom" in {
      ( new MiniSAT ).solve( SATProblems.getProblem1() ) must beLike {
        case Some( model ) => ok
        case None          => ko
      }
    }

    "see that Pc and -Pc is unsat" in {
      ( new MiniSAT ).solve( SATProblems.getProblem2() ) must beLike {
        case Some( _ ) => ko
        case None      => ok
      }
    }

    "see that Pc or -Pc is valid" in {
      ( new MiniSAT ).isValid( SATProblems.getProblem3a() ) must beTrue
      ( new MiniSATProver ).isValid( SATProblems.getProblem3b() ) must beTrue
    }

    "see that Pc is not valid" in {
      ( new MiniSAT ).isValid( SATProblems.getProblem4() ) must beFalse
    }

    "return a correct model" in {
      ( new MiniSAT ).solve( SATProblems.getProblem5() ) must beLike {
        case Some( model ) => if ( SATProblems.checkSolution5( model ) ) ok else ko
        case None          => ko
      }
    }

    "deal correctly with the pigeonhole problem" in {
      val sol_a = SATProblems.getProblem6a().map( ( new MiniSAT ).isValid( _ ) )
      val sol_b = SATProblems.getProblem6b().map( ( new MiniSAT ).isValid( _ ) )

      sol_a must_== sol_a.map( x => false )
      sol_b must_== sol_b.map( x => true )
    }

    "say bottom is unsatisfiable" in {
      new MiniSAT().solve( Bottom() ) must beNone
    }

    "say top is satisfiable" in {
      new MiniSAT().solve( Top() ) must beSome
    }

  }
}
