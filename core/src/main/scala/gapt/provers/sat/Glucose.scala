package gapt.provers.sat

import gapt.formats.dimacs.{ DIMACS, readDRUP, writeDIMACS }
import gapt.utils.{ runProcess, withTempFile }
import os._
import gapt.proofs.rup.RupProof

object Glucose extends Glucose( "glucose" )
class Glucose( command: String* ) extends ExternalSATSolver( command: _* ) with DrupSolver {
  def runForProof( dimacsInput: String ): Option[String] =
    withTempFile.fromString( dimacsInput ) { dimacsInputFile =>
      withTempFile { dimacsOutputFile =>
        runProcess.withExitValue( command ++ Seq(
          "-certified", s"-certified-output=$dimacsOutputFile",
          dimacsInputFile.toString ) ) match {
          // Glucose segfaults when run with -certified on a satisfiable problem
          case ( 10 | 139, _ ) => /* SAT */ None
          case ( 20 | 134, _ ) => /* UNSAT */ Some( read(dimacsOutputFile) )
          case ( _, str ) =>
            throw new Exception( s"Error executing external sat prover $command:\n$str" )
        }
      }
    }

  def getDrupProof( cnf: DIMACS.CNF ): Option[RupProof] = {
    if ( cnf.isEmpty ) return None
    runForProof( writeDIMACS( cnf ) ) map { readDRUP( cnf, _ ) }
  }

}
