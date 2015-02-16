package at.logic.cli

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
  import at.logic.cli.GAPScalaInteractiveShellLibrary._
  import at.logic.language.lambda.types._
  import at.logic.language._
  import at.logic.language.hol._
  import at.logic.language.fol._
  import at.logic.proofs.lk._
  import at.logic.proofs.lk.base._
  import at.logic.proofs.lksk
  import at.logic.language.lambda.symbols._
  import at.logic.language.hol.logicSymbols._
  import at.logic.proofs.hoare._
  import at.logic.proofs.algorithms.skolemization.skolemize
  import at.logic.algorithms.lk.regularize
  import at.logic.calculi.occurrences.FormulaOccurrence
  import at.logic.proofs.lk.algorithms.cutIntroduction.Deltas._
  import at.logic.algorithms.lk.statistics._
  import at.logic.provers.minisat.MiniSATProver
  import at.logic.gui.prooftool.gui.{Main => PT}
  import help.{apply => help}
  import at.logic.cli.GPL.{apply => copying, printLicense => license}
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
