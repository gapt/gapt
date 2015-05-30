package at.logic.gapt.cli

import scala.sys.SystemProperties
import scala.tools.nsc.interpreter._
import scala.tools.nsc.Settings

object CLIMain {

  val welcomeMessage = """
    *************************************
    *    Welcome to the GAPT shell!     *
    *                                   *
    *  See help for a list of commands. *
    *************************************

 Copyright (C) 2009-2015  GAPT developers

 This program comes with ABSOLUTELY NO WARRANTY. This is free
 software, and you are welcome to redistribute it under certain
 conditions; type `copying' for details.
"""

  val imports = """
  import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary._
  import at.logic.gapt.expr._
  import at.logic.gapt.language._
  import at.logic.gapt.language.hol._
  import at.logic.gapt.language.fol._
  import at.logic.gapt.proofs.lk._
  import at.logic.gapt.proofs.lk.base._
  import at.logic.gapt.proofs.lksk
  import at.logic.gapt.proofs.hoare._
  import at.logic.gapt.proofs.algorithms.skolemization.skolemize
  import at.logic.gapt.proofs.lk.algorithms.regularize
  import at.logic.gapt.proofs.occurrences.FormulaOccurrence
  import at.logic.gapt.proofs.lk.algorithms.cutIntroduction.Deltas._
  import at.logic.gapt.proofs.lk.algorithms.getStatistics
  import at.logic.gapt.provers.minisat.MiniSATProver
  import at.logic.gapt.prooftool.{Main => PT}
  import help.{apply => help}
  import at.logic.gapt.cli.GPL.{apply => copying, printLicense => license}
  """

  def main( args: Array[String] ) {
    val settings = new Settings
    settings.Yreplsync.value = true
    settings.usejavacp.value = true

    new SystemProperties += ( "scala.shell.prompt" -> "\ngapt> " )

    val repl = new ILoop {
      override def printWelcome = {
        println( welcomeMessage )
        intp.beQuietDuring {
          print( "Importing gapt... " )
          processLine( imports )
          println( "done." )
        }

        // If invoked as ./cli.sh script.scala,
        // then load script.scala and exit.
        if ( args.length >= 1 ) {
          withFile( args( 0 ) ) { f => interpretAllFrom( f ) }
          sys.exit( 0 )
        }
      }
    }

    repl process settings
  }
}
