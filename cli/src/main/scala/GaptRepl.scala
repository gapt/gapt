package gapt.cli

import gapt.formats.ClasspathInputFile

import scala.tools.nsc.Settings
import scala.tools.nsc.interpreter.{ ILoop, InteractiveReader }

case class GaptRepl() {

  private val replSettings = new Settings
  replSettings.usejavacp.value = true
  replSettings.feature.value = true
  replSettings.deprecation.value = true
  replSettings.Yreplsync.value = true
  replSettings.language.value = {
    import replSettings.language.domain._
    ValueSet( postfixOps, implicitConversions )
  }

  sys.props( "scala.shell.prompt" ) = sys.props( "line.separator" ) + "gapt> "

  private val repl = new ILoop {
    override def createInterpreter() = {
      val predefCode: String = readPredefFile
      in = InteractiveReader()
      intp = new ILoopInterpreter()
      intp.beQuietDuring( intp.interpret( predefCode ) )
    }
    override def printWelcome() = print( welcomeMessage )
  }

  def run(): Unit = repl.process( replSettings )

  private def readPredefFile: String =
    ClasspathInputFile( predefFileName ).read
}
