/**
 * Interface to the MiniSAT solver.
 * Needs the command-line tool minisat to work.
 */

package at.logic.gapt.provers.minisat

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.TseitinCNF
import at.logic.gapt.expr.hol._
import at.logic.gapt.formats.dimacs.{ readDIMACS, writeDIMACS, DIMACSHelper }
import at.logic.gapt.models.Interpretation
import at.logic.gapt.proofs.{ HOLClause, HOLSequent }
import at.logic.gapt.provers.Prover
import java.io._
import at.logic.gapt.utils.{ withTempFile, runProcess }

import scala.collection.immutable.HashMap
import scala.io.Source

// Call MiniSAT to solve quantifier-free Formulas.
class MiniSAT extends at.logic.gapt.utils.logging.Stopwatch {

  var atom_map: Map[HOLFormula, Int] = new HashMap[HOLFormula, Int]

  // Checks if f is valid using MiniSAT.
  def isValid( f: HOLFormula ) = solve( Neg( f ) ) match {
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
        TseitinCNF( f1 )
      }
      case _ => {
        debug( "starting naive CNF-transformation..." )
        CNFp.toClauseList( f )
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
  def solve( clauses: List[HOLClause] ): Option[Interpretation] = {
    val helper = new DIMACSHelper( clauses )

    val minisat_in = writeDIMACS( helper )

    val sat = withTempFile { out =>
      withTempFile.fromString( minisat_in ) { in =>
        runProcess( Seq( "minisat", in, out ) )
        Source.fromFile( out ).mkString
      }
    }

    readDIMACS( sat, helper )
  }
}

class MiniSATProver extends Prover with at.logic.gapt.utils.logging.Logger with at.logic.gapt.utils.traits.ExternalProgram {
  def getLKProof( seq: HOLSequent ): Option[at.logic.gapt.proofs.lk.base.LKProof] =
    throw new Exception( "MiniSAT does not produce proofs!" )

  override def isValid( f: HOLFormula ): Boolean = {
    val sat = new MiniSAT()
    sat.isValid( f )
  }

  override def isValid( seq: HOLSequent ): Boolean = {
    val sat = new MiniSAT()
    trace( "calling MiniSAT.isValid( " + Imp( And( seq.antecedent.toList ), Or( seq.succedent.toList ) ) + ")" )
    sat.isValid( Imp( And( seq.antecedent.toList ), Or( seq.succedent.toList ) ) )
  }

  val isInstalled: Boolean =
    try {
      val box: List[HOLClause] = List()
      ( new MiniSAT ).solve( box )
      true
    } catch {
      case ex: IOException => false
    }

}
