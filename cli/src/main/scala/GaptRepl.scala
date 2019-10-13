package gapt.cli

import gapt.formats.ClasspathInputFile

import scala.tools.nsc.Settings
import scala.tools.nsc.interpreter.shell.{ ILoop, ShellConfig }
import scala.tools.nsc.interpreter.InteractiveReader

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

  private val shellConfiguration = ShellConfig( replSettings )

  sys.props( "scala.shell.prompt" ) = sys.props( "line.separator" ) + "gapt> "

  private val repl = new ILoop( shellConfiguration ) {
    override def createInterpreter( settings: Settings ) = {
      super.createInterpreter( settings )
      val predefCode: String = readPredefFile
      intp.beQuietDuring( intp.interpret( predefCode ) )
    }
    override def printWelcome() = print( welcomeMessage )
  }

  def run(): Unit = repl.run( replSettings )

  private def readPredefFile: String =
    ClasspathInputFile( predefFileName ).read
}
