package at.logic.gapt.provers.sat

import java.io.IOException

import at.logic.gapt.expr.Top
import at.logic.gapt.formats.dimacs._
import at.logic.gapt.utils.{ ExternalProgram, runProcess, withTempFile }

class ExternalSATSolver( val command: String* ) extends SATSolver with ExternalProgram {
  protected def runProgram( dimacsInput: String ): Option[String] =
    withTempFile.fromString( dimacsInput ) { dimacsInputFile =>
      withTempFile { dimacsOutputFile =>
        runProcess.withExitValue( command ++ Seq( dimacsInputFile.pathAsString, dimacsOutputFile.pathAsString ) ) match {
          case ( 10, _ ) => /* SAT */ Some( dimacsOutputFile.contentAsString )
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
