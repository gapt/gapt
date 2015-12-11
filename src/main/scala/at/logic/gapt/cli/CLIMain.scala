package at.logic.gapt.cli

import scala.io.Source
import scala.sys.SystemProperties
import scala.tools.nsc.interpreter._
import scala.tools.nsc.Settings

object CLIMain {

  val welcomeMessage = """
    *************************************
    *    Welcome to the GAPT shell!     *
    *************************************

 Copyright (C) 2009-2015  GAPT developers

 This program comes with ABSOLUTELY NO WARRANTY. This is free
 software, and you are welcome to redistribute it under certain
 conditions; type `copying' for details.
"""

  val imports = Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( "gapt-cli-prelude.scala" ) ).mkString

  def main( args: Array[String] ) {
    val settings = new Settings
    settings.Yreplsync.value = true
    settings.usejavacp.value = true

    new SystemProperties += ( "scala.shell.prompt" -> ( sys.props( "line.separator" ) + "gapt> " ) )

    val repl = new ILoop {
      override def printWelcome = {
        println( welcomeMessage )
        intp.beQuietDuring {
          print( "Importing gapt... " )
          processLine( imports )
          println( "done." )
        }

        // If invoked as ./gapt.sh script.scala,
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
