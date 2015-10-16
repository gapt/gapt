package at.logic.gapt.provers.sat

import java.io.IOException

import at.logic.gapt.expr.{ Neg, Top, FOLFormula, HOLFormula }
import at.logic.gapt.expr.fol.TseitinCNF
import at.logic.gapt.formats.dimacs.{ readDIMACS, writeDIMACS, DIMACSEncoding, DIMACS }
import at.logic.gapt.models.Interpretation
import at.logic.gapt.proofs.lkNew.LKProof
import at.logic.gapt.proofs.{ HOLSequent, HOLClause }
import at.logic.gapt.provers.Prover
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.{ runProcess, withTempFile }

import scala.io.Source

abstract class SATSolver extends Prover {

  def solve( cnf: DIMACS.CNF ): Option[DIMACS.Model]

  def solve( cnf: TraversableOnce[HOLClause] ): Option[Interpretation] = {
    val encoding = new DIMACSEncoding
    solve( encoding.encodeCNF( cnf ) ) map { dimacsModel =>
      encoding.decodeModel( dimacsModel )
    }
  }

  // FIXME: rewrite CNF transformation and support non-FOL clauses...
  def solve( formula: HOLFormula ): Option[Interpretation] =
    solve( TseitinCNF( formula.asInstanceOf[FOLFormula] ) )

  def getLKProof( seq: HOLSequent ): Option[LKProof] = throw new UnsupportedOperationException
  override def isValid( f: HOLFormula ): Boolean = solve( -f ).isEmpty
  override def isValid( seq: HOLSequent ): Boolean = isValid( seq.toFormula )
}

abstract class ExternalSATSolver extends SATSolver with ExternalProgram {
  def command: Seq[String]

  protected def runProgram( dimacsInput: String ): String =
    withTempFile.fromString( dimacsInput ) { dimacsInputFile =>
      withTempFile { dimacsOutputFile =>
        runProcess.withExitValue( command ++ Seq( dimacsInputFile, dimacsOutputFile ) )
        Source.fromFile( dimacsOutputFile ).mkString
      }
    }

  override def solve( cnf: DIMACS.CNF ): Option[DIMACS.Model] =
    readDIMACS( runProgram( writeDIMACS( cnf ) ) )

  override val isInstalled: Boolean =
    try solve( Top() ).isDefined catch { case _: IOException => false }
}