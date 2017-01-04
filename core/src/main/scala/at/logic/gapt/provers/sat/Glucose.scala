package at.logic.gapt.provers.sat

import at.logic.gapt.formats.dimacs.{ DIMACS, readDRUP, writeDIMACS }
import at.logic.gapt.utils.{ runProcess, withTempFile }

import ammonite.ops._

object Glucose extends Glucose( "glucose" )
class Glucose( command: String* ) extends ExternalSATSolver( command: _* ) with DrupSolver {
  def runForProof( dimacsInput: String ): Option[String] =
    withTempFile.fromString( dimacsInput ) { dimacsInputFile =>
      withTempFile { dimacsOutputFile =>
        runProcess.withExitValue( command ++ Seq(
          "-certified", s"-certified-output=$dimacsOutputFile",
          dimacsInputFile.toString
        ) ) match {
          // Glucose segfaults when run with -certified on a satisfiable problem
          case ( 10 | 139, _ ) => /* SAT */ None
          case ( 20 | 134, _ ) => /* UNSAT */ Some( read ! dimacsOutputFile )
          case ( 1, str ) =>
            throw new Exception( s"Error executing external sat prover $command: $str" )
        }
      }
    }

  def getDrupProof( cnf: DIMACS.CNF ): Option[DIMACS.DRUP] = {
    if ( cnf.isEmpty ) return None
    runForProof( writeDIMACS( cnf ) ) map { readDRUP( _ ) }
  }

}
