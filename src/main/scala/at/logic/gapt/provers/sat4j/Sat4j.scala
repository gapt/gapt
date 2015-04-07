/**
 * Interface to Sat4j solver.
 */

package at.logic.gapt.provers.sat4j

import at.logic.gapt.formats.dimacs.{ writeDIMACS, readDIMACS, DIMACSHelper }
import at.logic.gapt.language.hol.HOLFormula
import at.logic.gapt.proofs.resolution.algorithms.{ CNFp, TseitinCNF }
import at.logic.gapt.utils.logging.{ Stopwatch, Logger }
import at.logic.gapt.language.fol.FOLFormula
import at.logic.gapt.language.hol._
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.lk.base.{ LKProof, FSequent }
import at.logic.gapt.provers.Prover
import at.logic.gapt.models._
import java.io.BufferedWriter
import java.io.File
import java.io.FileOutputStream
import java.io.FileWriter
import java.io.OutputStreamWriter
import org.sat4j.reader.DimacsReader
import org.sat4j.specs.ContradictionException
import org.sat4j.specs.IProblem

object readSat4j extends Logger {
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
class Sat4j extends Stopwatch {
  // Checks if f is valid using Sat4j.
  def isValid( f: HOLFormula ) = solve( HOLNeg( f ) ) match {
    case Some( _ ) => false
    case None      => true
  }

  // Returns a model of the formula obtained from the Sat4j SAT solver.
  // Returns None if unsatisfiable.
  def solve( f: HOLFormula ): Option[Interpretation] = {
    start()
    val cnf = f match {
      case f1: FOLFormula => TseitinCNF( f1 )
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
      trace( sat4j_in )

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

class Sat4jProver extends Prover with Logger {
  def getLKProof( seq: FSequent ): Option[LKProof] =
    throw new Exception( "Sat4j does not produce proofs!" )

  override def isValid( f: HOLFormula ): Boolean = {
    val sat = new Sat4j()
    sat.isValid( f )
  }

  override def isValid( seq: FSequent ): Boolean = {
    val sat = new Sat4j()
    trace( "calling Sat4j.isValid( " + HOLImp( HOLAnd( seq.antecedent.toList ), HOLOr( seq.succedent.toList ) ) + ")" )
    sat.isValid( HOLImp( HOLAnd( seq.antecedent.toList ), HOLOr( seq.succedent.toList ) ) )
  }

}
