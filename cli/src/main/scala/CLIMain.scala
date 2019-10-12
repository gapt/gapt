package gapt.cli

import gapt.examples.Script
import gapt.formats.ClasspathInputFile

import scala.tools.nsc.interpreter._
import scala.tools.nsc.Settings
import ammonite.ops._

object CLIMain {

  val welcomeMessage = """
    *************************************
    *    Welcome to the GAPT shell!     *
    *************************************

 Copyright (C) 2009-2019  GAPT developers

 This program comes with ABSOLUTELY NO WARRANTY. This is free
 software, and you are welcome to redistribute it under certain
 conditions; type `copying' for details.
"""

  val imports = ClasspathInputFile( "gapt-cli-prelude.scala", getClass ).read

  class ScriptsResultHolder( var result: Seq[Script] = Seq() ) {
    def add( script: Script ): Unit = result :+= script
  }

  def main( args: Array[String] ): Unit = {

    args match {

      // If invoked as ./gapt.sh `script`, then execute `script` and exit.
      case Array( scriptFile, scriptArgs @ _* ) =>
        GaptScriptInterpreter.run( scriptFile, scriptArgs )

      case _ =>
        GaptRepl().run()
    }
  }

}
