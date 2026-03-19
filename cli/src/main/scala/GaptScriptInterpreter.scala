package gapt.cli

import os.{Path, pwd, read}
import gapt.formats.ClasspathInputFile
import dotty.tools.repl._

object GaptScriptInterpreter {
  def run(scriptFileName: String, scriptArguments: Seq[String]): Unit = {

    val repl = new dotty.tools.repl.ReplDriver(
      Array(
        "-usejavacp",
        "-feature",
        "-deprecation",
        "-language:postfixOps",
        "-language:implicitConversions"
      )
    )

    val initialState = repl.initialState.copy(quiet = true)
    val state = repl.run(readPredefFile)(using initialState)
    // Strip package declaration, the script compiler doesn't like it.
    val packageRegex = """(?s)package [A-Za-z.]+\n(.*)""".r
    val scriptSrc = read(Path(scriptFileName, pwd)) match {
      case packageRegex(restOfScript) => restOfScript
      case scriptWithoutPackage       => scriptWithoutPackage
    }
    repl.run(s"""
           |val args: Array[String] = Array(${scriptArguments.map(quote).mkString(",")})
           |${scriptSrc}
           |""".stripMargin)(using state)
  }

  private def readPredefFile: String =
    ClasspathInputFile(predefFileName).read

  private def quote(string: String): String = s"""\"\"\"$string\"\"\""""

}
