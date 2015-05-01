/*
 * Tests for the MiniSAT interface.
**/

package at.logic.gapt.provers.minisat

import java.io.IOException

import at.logic.gapt.models.Interpretation
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.gapt.language.fol._
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.lk.base.FSequent

object SATProblems {
  object PigeonHolePrinciple {
    // The binary relation symbol.
    val rel = "R"

    def apply( ps: Int, hs: Int ) = {
      assert( ps > 1 )
      FOLImp( FOLAnd( ( 1 to ps ).map( p =>
        FOLOr( ( 1 to hs ).map( h => atom( p, h ) ).toList ) ).toList ),
        FOLOr( ( 1 to hs ).map( h =>
          FOLOr( ( 2 to ps ).map( p =>
            FOLOr( ( ( 1 to p - 1 ) ).map( pp =>
              FOLAnd( atom( p, h ), atom( pp, h ) ) ).toList ) ).toList ) ).toList ) )
    }

    def atom( p: Int, h: Int ) = FOLAtom( rel, pigeon( p ) :: hole( h ) :: Nil )

    def pigeon( i: Int ) = FOLConst( "p_" + i )

    def hole( i: Int ) = FOLConst( "h_" + i )
  }

  val c = FOLConst( "c" )
  val d = FOLConst( "d" )
  val e = FOLConst( "e" )
  val pc = FOLAtom( "P", c :: Nil )
  val pd = FOLAtom( "P", d :: Nil )
  val pe = FOLAtom( "P", e :: Nil )

  def getProblem1() = FClause( Nil, pc :: Nil ) :: Nil
  def getProblem2() = {
    val c1 = FClause( Nil, pc :: Nil )
    val c2 = FClause( pc :: Nil, Nil )
    c1 :: c2 :: Nil
  }
  def getProblem3a() = FOLOr( pc, FOLNeg( pc ) )
  def getProblem3b() = new FSequent( Nil, FOLOr( pc, FOLNeg( pc ) ) :: Nil )
  def getProblem4() = pc
  def getProblem5() = {
    val c1 = FClause( Nil, pc :: Nil )
    val c2 = FClause( pc :: Nil, pd :: Nil )
    val c3 = FClause( pd :: pe :: Nil, Nil )
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

@RunWith( classOf[JUnitRunner] )
class MiniSATTest extends SpecificationWithJUnit {
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
      new MiniSAT().solve( FOLBottomC ) must beNone
    }

    "say top is satisfiable" in {
      new MiniSAT().solve( FOLTopC ) must beLike {
        case Some( _ ) => ok
        case None      => ko
      }
    }

  }
}
