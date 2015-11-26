package at.logic.gapt.provers.maxsat

import java.io.IOException

import at.logic.gapt.expr.FOLAtom
import at.logic.gapt.formats.dimacs.{ writeWDIMACS, readWDIMACS, DIMACS }
import at.logic.gapt.utils.{ withTempFile, runProcess }
import at.logic.gapt.utils.traits.ExternalProgram

class ExternalMaxSATSolver( val command: String* ) extends MaxSATSolver with ExternalProgram {
  protected def runProgram( dimacsInput: String ): String =
    withTempFile.fromString( dimacsInput ) { inFile =>
      runProcess.withExitValue( command :+ inFile )._2
    }

  def solve( hard: DIMACS.CNF, soft: Seq[( DIMACS.Clause, Int )] ): Option[DIMACS.Model] =
    readWDIMACS( runProgram( writeWDIMACS( hard, soft ) ) )

  val isInstalled =
    try solve( FOLAtom( "p" ), Seq( -FOLAtom( "p" ) -> 10 ) ).isDefined
    catch { case _: IOException => false }
}

object OpenWBO extends ExternalMaxSATSolver( "open-wbo" )
object MiFuMaX extends ExternalMaxSATSolver( "mifumax" )
object ToySolver extends ExternalMaxSATSolver( "toysolver", "--maxsat" )
object ToySAT extends ExternalMaxSATSolver( "toysat", "--maxsat" )
object MiniMaxSAT extends ExternalMaxSATSolver( "minimaxsat", "-F=2" )
object QMaxSAT extends ExternalMaxSATSolver( "qmaxsat" )
