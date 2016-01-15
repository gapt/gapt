package at.logic.gapt.cli

import scala.io.Source
import scala.tools.nsc.interpreter._
import scala.tools.nsc.Settings
import at.logic.gapt.utils.logging.Logger

object CLIMain extends Logger {

  val welcomeMessage = """
    *************************************
    *    Welcome to the GAPT shell!     *
    *************************************

 Copyright (C) 2009-2016  GAPT developers

 This program comes with ABSOLUTELY NO WARRANTY. This is free
 software, and you are welcome to redistribute it under certain
 conditions; type `copying' for details.
"""

  val imports = Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( "gapt-cli-prelude.scala" ) ).mkString

  def main( args: Array[String] ) {
    val settings = new Settings
    settings.usejavacp.value = true
    settings.language.value = {
      import settings.language.domain._
      ValueSet( postfixOps, implicitConversions )
    }
    settings.feature.value = true
    settings.deprecation.value = true

    args match {

      // If invoked as ./gapt.sh script.scala,
      // then load script.scala and exit.
      case Array( scriptFile ) =>
        debug( "Initializing logging framework" )
        new IMain( settings ).compile( imports + Source.fromFile( scriptFile ).mkString ).eval()

      case _ =>
        settings.Yreplsync.value = true

        sys.props( "scala.shell.prompt" ) = sys.props( "line.separator" ) + "gapt> "

        val repl = new ILoop {
          override def printWelcome = {
            println( welcomeMessage )
            intp beQuietDuring {
              print( "Importing gapt... " )
              processLine( imports )
              println( "done." )
            }
          }
        }

        repl process settings

    }
  }

}
