/**
 * Interface to the MiniSAT solver.
 * Needs the command-line tool minisat to work.
 */

package at.logic.gapt.provers.minisat

import at.logic.gapt.formats.dimacs.{ readDIMACS, writeDIMACS, DIMACSHelper }
import at.logic.gapt.language.fol.FOLFormula
import at.logic.gapt.language.hol._
import at.logic.gapt.models.Interpretation
import at.logic.gapt.proofs.resolution._
import java.io._
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.proofs.resolution.algorithms.{ TseitinCNF, CNFp }
import at.logic.gapt.provers.Prover
import scala.collection.immutable.HashMap

// Call MiniSAT to solve quantifier-free HOLFormulas.
class MiniSAT extends at.logic.gapt.utils.logging.Stopwatch {

  var atom_map: Map[HOLFormula, Int] = new HashMap[HOLFormula, Int]

  // Checks if f is valid using MiniSAT.
  def isValid( f: HOLFormula ) = solve( HOLNeg( f ) ) match {
    case Some( _ ) => false
    case None      => true
  }

  // Returns a model of the formula obtained from the MiniSAT SAT solver.
  // Returns None if unsatisfiable.
  def solve( f: HOLFormula ): Option[Interpretation] = {
    start()
    val cnf = f match {
      case f1: FOLFormula => {
        debug( "starting Tseitin CNF-transformation..." )
        TseitinCNF( f1 )._1
      }
      case _ => {
        debug( "starting naive CNF-transformation..." )
        CNFp( f )
      }
    }
    debug( "CNF-transformation finished." )
    lap( "CNF done" )
    val int = solve( cnf )
    lap( "Solving done" )
    int
  }

  // Returns a model of the set of clauses obtained from the MiniSAT SAT solver.
  // Returns None if unsatisfiable.
  def solve( clauses: List[FClause] ): Option[Interpretation] =
    {
      val helper = new DIMACSHelper( clauses )

      val minisat_in = writeDIMACS( helper )
      trace( "Generated MiniSAT input: " )
      trace( minisat_in );

      val temp_in = File.createTempFile( "gapt_minisat_in", ".sat" )
      temp_in.deleteOnExit()

      val temp_out = File.createTempFile( "gapt_minisat_out", ".sat" )
      temp_out.deleteOnExit()

      val out = new BufferedWriter( new FileWriter( temp_in ) )
      out.append( minisat_in )
      out.close()

      // run minisat

      val bin = "minisat";
      val run = bin + " " + temp_in.getAbsolutePath() + " " + temp_out.getAbsolutePath();
      debug( "Starting minisat..." );
      val p = Runtime.getRuntime().exec( run );
      p.waitFor();
      debug( "minisat finished." );

      // parse minisat output and construct map
      val sat = scala.io.Source.fromFile( temp_out ).mkString;

      trace( "MiniSAT result: " + sat )

      readDIMACS( sat, helper )
    }
}

class MiniSATProver extends Prover with at.logic.gapt.utils.logging.Logger with at.logic.gapt.utils.traits.ExternalProgram {
  def getLKProof( seq: FSequent ): Option[at.logic.gapt.proofs.lk.base.LKProof] =
    throw new Exception( "MiniSAT does not produce proofs!" )

  override def isValid( f: HOLFormula ): Boolean = {
    val sat = new MiniSAT()
    sat.isValid( f )
  }

  override def isValid( seq: FSequent ): Boolean = {
    val sat = new MiniSAT()
    trace( "calling MiniSAT.isValid( " + HOLImp( HOLAnd( seq.antecedent.toList ), HOLOr( seq.succedent.toList ) ) + ")" )
    sat.isValid( HOLImp( HOLAnd( seq.antecedent.toList ), HOLOr( seq.succedent.toList ) ) )
  }

  def isInstalled(): Boolean =
    try {
      val box: List[FClause] = List()
      ( new MiniSAT ).solve( box )
      true
    } catch {
      case ex: IOException => false
    }

}
