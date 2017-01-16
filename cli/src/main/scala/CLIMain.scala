package at.logic.gapt.cli

import at.logic.gapt.examples.Script
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.utils.Logger

import scala.tools.nsc.interpreter._
import scala.tools.nsc.Settings
import ammonite.ops._

object CLIMain extends Logger {

  val welcomeMessage = """
    *************************************
    *    Welcome to the GAPT shell!     *
    *************************************

 Copyright (C) 2009-2017  GAPT developers

 This program comes with ABSOLUTELY NO WARRANTY. This is free
 software, and you are welcome to redistribute it under certain
 conditions; type `copying' for details.
"""

  val imports = ClasspathInputFile( "gapt-cli-prelude.scala", getClass ).read

  class ScriptsResultHolder( var result: Seq[Script] = Seq() ) {
    def add( script: Script ): Unit = result :+= script
  }

  def main( args: Array[String] ): Unit = {
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
      case Array( scriptFile, scriptArgs @ _* ) =>
        debug( "Initializing logging framework" )

        // Strip package declaration, the script compiler doesn't like it.
        val packageRegex = """(?s)package [A-Za-z.]+\n(.*)""".r
        val scriptSrc = read( Path( scriptFile, pwd ) ) match {
          case packageRegex( restOfScript ) => restOfScript
          case scriptWithoutPackage         => scriptWithoutPackage
        }

        val intp = new IMain( settings )
        intp.beQuietDuring {
          intp.interpret( imports + scriptSrc )

          val scriptsName = intp.naming.freshUserTermName()
          val scripts = new ScriptsResultHolder
          intp.bind( scriptsName.toString, scripts )

          // Execute all defined objects of type Script.
          // TODO(gabriel): use reflection again
          for {
            defTerm <- intp.namedDefinedTerms
            if intp.typeOfTerm( defTerm.toString ) <:< intp.global.typeOf[Script]
          } intp.interpret( s"$scriptsName.add($defTerm)\n" )

          for ( script <- scripts.result )
            script.main( scriptArgs.toArray )
        }

      case _ =>
        settings.Yreplsync.value = true

        sys.props( "scala.shell.prompt" ) = sys.props( "line.separator" ) + "gapt> "

        val repl = new ILoop {
          override def createInterpreter() = {
            in = InteractiveReader()
            intp = new ILoopInterpreter()
            intp.setContextClassLoader()
            intp.beQuietDuring( intp.interpret( imports ) )
          }
          override def printWelcome() = print( welcomeMessage )
        }

        repl process settings

    }
  }

}
