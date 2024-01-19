package gapt.cli

import gapt.examples.Script
import gapt.formats.ClasspathInputFile

import scala.tools.nsc.interpreter._
import scala.tools.nsc.Settings
import os._

object CLIMain {

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
