package at.logic.gapt.provers.sat

import java.io.IOException

import at.logic.gapt.expr.Top
import at.logic.gapt.formats.dimacs.{ writeDIMACS, readDIMACS, DIMACS }
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.{ runProcess, withTempFile }

import scala.io.Source

class ExternalSATSolver( val command: String* ) extends SATSolver with ExternalProgram {
  protected def runProgram( dimacsInput: String ): Option[String] =
    withTempFile.fromString( dimacsInput ) { dimacsInputFile =>
      withTempFile { dimacsOutputFile =>
        runProcess.withExitValue( command ++ Seq( dimacsInputFile, dimacsOutputFile ) ) match {
          case ( 10, _ ) => /* SAT */ Some( Source.fromFile( dimacsOutputFile ).mkString )
          case ( 20, _ ) => /* UNSAT */ None
          case ( 1, str ) =>
            throw new Exception( s"Error executing external sat prover $command: $str" )
        }
      }
    }

  override def solve( cnf: DIMACS.CNF ): Option[DIMACS.Model] =
    runProgram( writeDIMACS( cnf ) ) map { readDIMACS( _ ) }

  override val isInstalled: Boolean =
    try solve( Top() ).isDefined catch { case _: IOException => false }

  override def toString =
    s"ExternalSATSolver(${command map { '"' + _ + '"' } mkString ", "})"
}

object MiniSAT extends ExternalSATSolver( "minisat" )
object Glucose extends ExternalSATSolver( "glucose" )
