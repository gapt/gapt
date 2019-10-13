package gapt.cli

import ammonite.ops.{ Path, pwd, read }

import gapt.formats.ClasspathInputFile

import scala.tools.nsc.Settings
import scala.tools.nsc.interpreter.IMain

object GaptScriptInterpreter {

  private val settings = new Settings
  settings.usejavacp.value = true
  settings.language.value = {
    import settings.language.domain._
    ValueSet( postfixOps, implicitConversions )
  }
  settings.feature.value = true
  settings.deprecation.value = true

  def run( scriptFileName: String, scriptArguments: Seq[String] ): Unit = {
    val predefCode: String = readPredefFile
    // Strip package declaration, the script compiler doesn't like it.
    val packageRegex = """(?s)package [A-Za-z.]+\n(.*)""".r
    val scriptSrc = read( Path( scriptFileName, pwd ) ) match {
      case packageRegex( restOfScript ) => restOfScript
      case scriptWithoutPackage         => scriptWithoutPackage
    }
    val interpreter = new IMain( settings )
    interpreter.beQuietDuring {
      interpreter.interpret( predefCode )
      interpreter.interpret(
        s"""
           |val args: Array[String] = Array(${scriptArguments.map( quote ).mkString( "," )})
           |${scriptSrc}
           |""".stripMargin )
    }
  }

  private def readPredefFile: String =
    ClasspathInputFile( predefFileName ).read

  private def quote( string: String ): String = s"""\"\"\"$string\"\"\""""

}
