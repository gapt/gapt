package at.logic.gapt.provers.sat

import java.io.IOException

import at.logic.gapt.expr.Top
import at.logic.gapt.formats.dimacs.{ DIMACS, readDIMACS, readDRUP, writeDIMACS }
import at.logic.gapt.utils.{ ExternalProgram, runProcess, withTempFile }

import scala.io.Source

private object picoSatHelper {
  def getDefaultExecutableName() =
    try {
      // Debian and Fedora have a special name for PicoSAT with proof support
      val name = "picosat.trace"
      runProcess( Seq( name, "--version" ) )
      name
    } catch {
      case _: IOException =>
        "picosat"
    }
}

object PicoSAT extends PicoSAT( picoSatHelper.getDefaultExecutableName() )
class PicoSAT( command: String* ) extends DrupSolver with ExternalProgram {
  def runProgram( dimacsInput: String ): Either[String, String] =
    withTempFile.fromString( dimacsInput ) { dimacsInputFile =>
      withTempFile { drupOutputFile =>
        withTempFile { modelOutputFile =>
          runProcess.withExitValue( command ++ Seq(
            "-r", drupOutputFile,
            "-o", modelOutputFile,
            dimacsInputFile
          ) ) match {
            case ( 10, _ ) => /* SAT */ Right( Source.fromFile( modelOutputFile ).mkString )
            case ( 20, _ ) => /* UNSAT */ Left( Source.fromFile( drupOutputFile ).mkString )
            case ( 1, str ) =>
              throw new Exception( s"Error executing external sat prover $command: $str" )
          }
        }
      }
    }

  override def solve( cnf: DIMACS.CNF ): Option[DIMACS.Model] =
    runProgram( writeDIMACS( cnf ) ) match {
      case Right( model ) => Some( readDIMACS( model ) )
      case Left( proof )  => None
    }

  override val isInstalled: Boolean =
    try getDrupProof( Top() ).isDefined catch { case _: IOException => false }

  def getDrupProof( cnf: DIMACS.CNF ): Option[DIMACS.DRUP] =
    runProgram( writeDIMACS( cnf ) ) match {
      case Left( proof )  => Some( readDRUP( proof ) )
      case Right( model ) => None
    }

}
