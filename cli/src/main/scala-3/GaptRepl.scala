package gapt.cli

import gapt.formats.ClasspathInputFile
import dotty.tools.repl._

case class GaptRepl() {
  sys.props( "scala.shell.prompt" ) = sys.props( "line.separator" ) + "gapt> "

  def run(): Unit = 
    val repl = new dotty.tools.repl.ReplDriver(
      Array(
        "-usejavacp", 
        "-feature", 
        "-deprecation", 
        "-language:postfixOps", 
        "-language:implicitConversions"
      ))
    val state = repl.runQuietly(readPredefFile)(using repl.initialState)
    repl.runUntilQuit(using state)()

  private def readPredefFile: String =
    ClasspathInputFile( predefFileName ).read
}
