package gapt.cli

import os.{ Path, pwd, read }
import gapt.formats.ClasspathInputFile
import dotty.tools.repl._

object GaptScriptInterpreter {
  def run( scriptFileName: String, scriptArguments: Seq[String] ): Unit = {

    val repl = new dotty.tools.repl.ReplDriver(
      Array(
        "-usejavacp", 
        "-feature", 
        "-deprecation", 
        "-language:postfixOps", 
        "-language:implicitConversions"
      ))

    val state = repl.runQuietly(readPredefFile)(using repl.initialState)
    // Strip package declaration, the script compiler doesn't like it.
    val packageRegex = """(?s)package [A-Za-z.]+\n(.*)""".r
    val scriptSrc = read( Path( scriptFileName, pwd ) ) match {
      case packageRegex( restOfScript ) => restOfScript
      case scriptWithoutPackage         => scriptWithoutPackage
    }
    repl.runQuietly(s"""
           |val args: Array[String] = Array(${scriptArguments.map( quote ).mkString( "," )})
           |${scriptSrc}
           |""".stripMargin)(using state)
  }

  private def readPredefFile: String =
    ClasspathInputFile( predefFileName ).read

  private def quote( string: String ): String = s"""\"\"\"$string\"\"\""""

}
