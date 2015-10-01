/**
 * Interface to Sat4j solver.
 */

package at.logic.gapt.provers.sat4j

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.TseitinCNF
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.formats.dimacs.{ writeDIMACS, readDIMACS, DIMACSHelper }
import at.logic.gapt.models._
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.proofs.{ HOLClause, HOLSequent }
import at.logic.gapt.provers.Prover
import at.logic.gapt.utils.logging.{ Stopwatch, Logger }
import java.io._
import org.sat4j.reader.DimacsReader
import org.sat4j.specs.ContradictionException
import org.sat4j.specs.IProblem

object readSat4j extends Logger {
  def apply( problem: IProblem, helper: DIMACSHelper ) = {
    val nLine = sys.props( "line.separator" )

    val sat = new StringBuilder

    if ( problem.isSatisfiable() ) {
      sat append ( "SAT" + nLine )
      val model = problem.model()
      val sb = new StringBuffer()
      for ( i <- 0 until model.length ) {
        sb.append( model( i ) )
        sb.append( " " )
      }
      sb.append( "0" + nLine );
      sat append sb.toString
    } else {
      sat append ( "UNSAT" + nLine )
    }

    readDIMACS( sat.result(), helper )
  }
}

// Call Sat4j to solve quantifier-free Formulas.
class Sat4j {
  // Checks if f is valid using Sat4j.
  def isValid( f: HOLFormula ) = solve( Neg( f ) ) match {
    case Some( _ ) => false
    case None      => true
  }

  // Returns a model of the formula obtained from the Sat4j SAT solver.
  // Returns None if unsatisfiable.
  def solve( f: HOLFormula ): Option[Interpretation] = {
    val cnf = f match {
      case f1: FOLFormula => TseitinCNF( f1 )
      case _              => CNFp.toClauseList( f )
    }
    solve( cnf )
  }

  // Returns a model of the set of clauses obtained from the Sat4j SAT solver.
  // Returns None if unsatisfiable.
  def solve( clauses: List[HOLClause] ): Option[Interpretation] =
    {
      val helper = new DIMACSHelper( clauses )

      val sat4j_in = writeDIMACS( helper )

      // run Sat4j

      val solver = org.sat4j.minisat.SolverFactory.newDefault()
      val res =
        try {
          val problem = new DimacsReader( solver ).parseInstance( new ByteArrayInputStream( sat4j_in.getBytes ) )
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
  def getLKProof( seq: HOLSequent ): Option[LKProof] =
    throw new Exception( "Sat4j does not produce proofs!" )

  override def isValid( f: HOLFormula ): Boolean = {
    val sat = new Sat4j()
    sat.isValid( f )
  }

  override def isValid( seq: HOLSequent ): Boolean = {
    val sat = new Sat4j()
    trace( "calling Sat4j.isValid( " + Imp( And( seq.antecedent.toList ), Or( seq.succedent.toList ) ) + ")" )
    sat.isValid( Imp( And( seq.antecedent.toList ), Or( seq.succedent.toList ) ) )
  }

}
