/**
 * Interface to Sat4j solver.
 */

package at.logic.gapt.provers.sat4j

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.TseitinCNF
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.formats.dimacs.{ writeDIMACS, readDIMACS, DIMACSHelper }
import at.logic.gapt.models._
import at.logic.gapt.proofs.lkNew.LKProof
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

