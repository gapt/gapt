/**
 * Interface to Sat4j solver.
 */

package at.logic.provers.sat4j

import at.logic.language.fol.FOLFormula
import at.logic.language.hol._
import at.logic.calculi.resolution._
import at.logic.algorithms.resolution.{ CNFp, TseitinCNF }

import java.io._
import java.lang.StringBuilder

import at.logic.calculi.lk.base.FSequent

import at.logic.provers.Prover

import at.logic.models._

import at.logic.parsing.language.dimacs.DIMACSExporter

import scala.collection.immutable.HashMap

import java.io.BufferedReader
import java.io.BufferedWriter
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.FileWriter
import java.io.IOException
import java.io.InputStreamReader
import java.io.OutputStreamWriter

import org.sat4j.minisat.SolverFactory
import org.sat4j.reader.DimacsReader
import org.sat4j.reader.Reader
import org.sat4j.specs.ContradictionException
import org.sat4j.specs.IProblem
import org.sat4j.specs.ISolver

// Call Sat4j to solve quantifier-free HOLFormulas.
class Sat4j extends at.logic.utils.logging.Stopwatch {

  var atom_map: Map[HOLFormula, Int] = new HashMap[HOLFormula, Int]

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
      val dimacs = new DIMACSExporter( clauses )

      val sat4j_in = dimacs.getDIMACSString()
      trace( "Generated Sat4j input: " )
      trace( sat4j_in );

      val temp_in = File.createTempFile( "agito_sat4j_in", ".sat" )
      temp_in.deleteOnExit()

      val temp_out = File.createTempFile( "agito_sat4j_out", ".sat" )
      temp_out.deleteOnExit()

      val out = new BufferedWriter( new FileWriter( temp_in ) )
      out.append( sat4j_in )
      out.close()

      // run Sat4j

      debug( "Starting sat4j..." );
      val sat4jSolver: ISolver = SolverFactory.newDefault()
      val reader: Reader = new DimacsReader( sat4jSolver )
      val writer = new BufferedWriter( new OutputStreamWriter(
        new FileOutputStream( temp_out ), "UTF-8" ) )
      try {
        val problem: IProblem = reader.parseInstance( temp_in.getAbsolutePath() )
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
      } catch {
        case e: ContradictionException => {
          writer.write( "UNSAT\n" )
        }
      } finally {
        writer.close()
        sat4jSolver.reset
      }
      debug( "Sat4j finished." )
      // parse sat4j output and construct map
      val sat = scala.io.Source.fromFile( temp_out ).mkString;

      trace( "Sat4j result: " + sat )

      dimacs.getInterpretation( sat )
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
