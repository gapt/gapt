/**
 * Interface to Sat4j solver.
 */

package at.logic.provers.sat4j

import at.logic.language.fol.FOLFormula
import at.logic.language.hol._
import at.logic.calculi.resolution._
import at.logic.algorithms.resolution.{ CNFp, TseitinCNF }

import at.logic.calculi.lk.base.FSequent
import at.logic.parsing.language.dimacs.{ readDIMACS, writeDIMACS, DIMACSHelper }

import at.logic.provers.Prover

import at.logic.models._
import at.logic.provers.maxsat.{ WDIMACSHelper, MaxSATSolver }

import java.io.BufferedWriter
import java.io.File
import java.io.FileOutputStream
import java.io.FileWriter
import java.io.OutputStreamWriter

import org.sat4j.reader.DimacsReader
import org.sat4j.reader.Reader
import org.sat4j.specs.ContradictionException
import org.sat4j.specs.IProblem
import org.sat4j.specs.ISolver

object readSat4j extends at.logic.utils.logging.Logger {
  def apply( problem: IProblem, helper: DIMACSHelper ) = {
    val temp_out = File.createTempFile( "gapt_sat4j_out", ".sat" )
    temp_out.deleteOnExit()

    val writer = new BufferedWriter( new OutputStreamWriter(
      new FileOutputStream( temp_out ), "UTF-8" ) )

    if ( problem.isSatisfiable() ) {
      writer.write( "SAT\n" )
      val model = problem.model()
      val sb = new StringBuffer()
      for ( i <- 0 until model.length ) {
        sb.append( model( i ) )
        sb.append( " " );
      }
      sb.append( "0\n" );
      writer.write( sb.toString )
    } else {
      writer.write( "UNSAT\n" )
    }
    writer.close()

    debug( "Sat4j finished." )
    // parse sat4j output and construct map
    val sat = scala.io.Source.fromFile( temp_out ).mkString;

    trace( "Sat4j result: " + sat )

    readDIMACS( sat, helper )
  }
}

// Call Sat4j to solve quantifier-free HOLFormulas.
class Sat4j extends at.logic.utils.logging.Stopwatch {
  // Checks if f is valid using Sat4j.
  def isValid( f: HOLFormula ) = solve( Neg( f ) ) match {
    case Some( _ ) => false
    case None      => true
  }

  // Returns a model of the formula obtained from the Sat4j SAT solver.
  // Returns None if unsatisfiable.
  def solve( f: HOLFormula ): Option[Interpretation] = {
    start()
    val cnf = f match {
      case f1: FOLFormula => TseitinCNF( f1 )._1
      case _              => CNFp( f )
    }
    lap( "CNF done" )
    val int = solve( cnf )
    lap( "Solving done" )
    int
  }

  // Returns a model of the set of clauses obtained from the Sat4j SAT solver.
  // Returns None if unsatisfiable.
  def solve( clauses: List[FClause] ): Option[Interpretation] =
    {
      val helper = new DIMACSHelper( clauses )

      val sat4j_in = writeDIMACS( helper )
      trace( "Generated Sat4j input: " )
      trace( sat4j_in );

      val temp_in = File.createTempFile( "gapt_sat4j_in", ".sat" )
      temp_in.deleteOnExit()

      val out = new BufferedWriter( new FileWriter( temp_in ) )
      out.append( sat4j_in )
      out.close()

      // run Sat4j

      debug( "Starting sat4j..." )
      val solver = org.sat4j.minisat.SolverFactory.newDefault()
      val res =
        try {
          val problem = new DimacsReader( solver ).parseInstance( temp_in.getAbsolutePath )
          readSat4j( problem, helper )
        } catch {
          case e: ContradictionException => None
        } finally {
          solver.reset
        }
      res
    }
}

class Sat4jProver extends Prover with at.logic.utils.logging.Logger {
  def getLKProof( seq: FSequent ): Option[at.logic.calculi.lk.base.LKProof] =
    throw new Exception( "Sat4j does not produce proofs!" )

  override def isValid( f: HOLFormula ): Boolean = {
    val sat = new Sat4j()
    sat.isValid( f )
  }

  override def isValid( seq: FSequent ): Boolean = {
    val sat = new Sat4j()
    trace( "calling Sat4j.isValid( " + Imp( And( seq.antecedent.toList ), Or( seq.succedent.toList ) ) + ")" )
    sat.isValid( Imp( And( seq.antecedent.toList ), Or( seq.succedent.toList ) ) )
  }

}
