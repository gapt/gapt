package at.logic.gapt.testing

import at.logic.gapt.cli.CLIMain

import scala.io.Source
import scala.reflect
import scala.sys.process
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
  var isSkipped = false

  class ResultHolder( var result: Any )
  def evalCodeInInterp( code: String ): Any = {
    val resultHolder = new ResultHolder( null )
    val varName = "$evalCodeSnippetsInLatex_result"
    interp beSilentDuring {
      interp.bind( varName, resultHolder )
      interp interpret s"$varName.result = ($code)"
    }
    resultHolder.result
  }

  val cliInputLine = """\s*gapt> (.*)""".r
  val beginCliListing = """\\begin\{clilisting\}(?:\[(.*)\])?""".r
  val endCliListing = """\end{clilisting}"""
  val assignment = """val\s+\w+\s+=.*""".r

  for ( line <- Source.fromFile( inFile ).getLines() )
    if ( inCliListing && isSkipped ) {
      println( line )
      line match {
        case `endCliListing` =>
          inCliListing = false
        case cliInputLine( assignment() ) =>
        case cliInputLine( _ ) =>
          // increment res123 counter
          interp beSilentDuring { interp command "true" }
        case _ =>
      }
    } else if ( inCliListing && !isSkipped ) {
      line match {
        case `endCliListing` =>
          println( line )
          inCliListing = false
        case line @ cliInputLine( command ) =>
          println( s"gapt> $command" )
          interp.command( command )
          println()
        case _ =>
      }
    } else {
      line match {
        case beginCliListing( condition ) =>
          println( line )
          inCliListing = true
          isSkipped = condition != null && evalCodeInInterp( condition ) != true
          if ( isSkipped )
            process.stderr println s"Skipping snippet because condition failed: $condition"
        case _ => println( line )
      }
    }

}
