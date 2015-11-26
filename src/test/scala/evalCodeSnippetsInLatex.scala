package at.logic.gapt.testing

import at.logic.gapt.cli.CLIMain

import scala.io.Source
import scala.reflect
import scala.tools.nsc.Settings
import scala.tools.nsc.interpreter._

object evalCodeSnippetsInLatex extends App {

  val Array( inFile ) = args

  def mkInterp(): ILoop = {
    val settings = new Settings
    settings.Yreplsync.value = true
    settings.usejavacp.value = true

    sys.props( "scala.shell.prompt" ) = "\ngapt> "

    val repl = new ILoop

    // the following is code that would be executed by repl.process()
    repl.settings = settings
    repl.createInterpreter()
    repl.in = SimpleReader()
    repl.intp.initializeSynchronous()
    repl.intp.quietBind( NamedParam[IMain]( "$intp", repl.intp )( StdReplTags.tagOfIMain, reflect.classTag[IMain] ) )
    repl.intp.setContextClassLoader()

    repl.intp.beQuietDuring {
      repl command CLIMain.imports

      // don't open prooftool
      repl command "def prooftool(x: Any): Unit = ()"

      // don't open help
      repl command "def help(x: Any*): Unit = ()"
    }

    repl
  }

  var interp = mkInterp()
  var inCliListing = false

  val cliInputLine = """\s*gapt> (.*)""".r

  for ( line <- Source.fromFile( inFile ).getLines() )
    if ( inCliListing )
      line match {
        case """\end{clilisting}""" =>
          println( line )
          inCliListing = false
        case line @ cliInputLine( command ) =>
          println( s"gapt> $command" )
          interp.command( command )
          println()
        case _ =>
      }
    else
      line match {
        case """\begin{clilisting}""" =>
          println( line )
          inCliListing = true
        case _ => println( line )
      }

}
