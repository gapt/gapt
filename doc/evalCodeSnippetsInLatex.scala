package at.logic.gapt.testing

import java.io.Writer

import at.logic.gapt.cli.CLIMain

import scala.sys.process
import scala.tools.nsc.Settings
import scala.tools.nsc.interpreter._
import ammonite.ops._

object evalCodeSnippetsInLatex {

  def mkInterp(): ILoop = {
    val settings = new Settings
    settings.Yreplsync.value = true
    settings.usejavacp.value = true

    sys.props( "scala.shell.prompt" ) = "\ngapt> "

    val repl = new ILoop( None, new JPrintWriter( new Writer() {
      val lambdaRegex = """(?<= )[A-Za-z.0-9]+\$\$Lambda\$\d+/\d+@[0-9a-f]+""".r

      override def flush() = Console.out.flush()
      override def write( cbuf: Array[Char], off: Int, len: Int ) = {
        val string = new String( cbuf, off, len )
        Console.out.print( lambdaRegex.replaceAllIn( string, "<function>" ) )
      }
      override def close() = {}
    } ) )

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
      repl command "def prooftool[T: at.logic.gapt.prooftool.ProoftoolViewable](x: T, name: String = \"\"): Unit = ()"

      // don't open help
      repl command "def help(x: Any*): Unit = ()"
    }

    repl
  }

  class ResultHolder( var result: Any )
  def evalCodeInInterp( code: String, interp: ILoop ): Any = {
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
  val beginTacticsListing = """\\begin\{tacticslisting\}(?:\[(.*)\])?""".r
  val endTacticsListing = """\end{tacticslisting}"""
  val beginTacticsOutput = """\begin{tacticsoutput}"""
  val endTacticsOutput = """\end{tacticsoutput}"""

  def processCliListing( listing: Seq[String], condition: String, interp: ILoop ): Unit = {
    if ( condition == null ) println( s"\\begin{clilisting}" ) else println( s"\\begin{clilisting}[$condition]" )
    if ( condition != null && evalCodeInInterp( condition, interp ) != true ) {
      process.stderr println s"Skipping snippet because condition failed: $condition"

      listing foreach println

      listing foreach {
        case cliInputLine( assignment() ) =>
        case cliInputLine( _ ) =>
          // increment res123 counter
          interp beSilentDuring { interp command "true" }
        case _ =>
      }
    } else {
      listing foreach {
        case cliInputLine( command ) =>
          println( s"gapt> $command" )
          interp.command( command )
          println()
        case _ =>
      }
    }
    println( endCliListing )
  }

  def processTacticsListing( listing: Seq[String], optionString: String, interp: ILoop ): Unit = {
    val options = if ( optionString == null ) Seq() else optionString.split( "," ).toSeq

    val code = new StringBuilder
    code ++= "val () = { new at.logic.gapt.proofs.gaptic.TacticsProof {\n"
    code ++= "import at.logic.gapt.proofs.gaptic._\n"
    if ( !options.contains( "nosig" ) )
      code ++= "implicit def sig = at.logic.gapt.formats.babel.BabelSignature.defaultSignature\n"
    for ( line <- listing ) { code ++= line; code += '\n' }
    code ++= "}; () }"

    println( """\begin{tacticslisting}""" +
      ( if ( options.isEmpty ) "" else s"[${options.mkString( "," )}]" ) )
    listing foreach println
    println( endTacticsListing )
    println( beginTacticsOutput )
    interp command code.result()
    println( endTacticsOutput )
  }

  def processLines( lines: Stream[String], interp: ILoop ): Unit = lines match {
    case beginCliListing( condition ) #:: rest =>
      processCliListing( rest takeWhile { _ != endCliListing }, condition, interp )
      processLines( rest dropWhile { _ != endCliListing } drop 1, interp )
    case beginTacticsListing( optionString ) #:: rest =>
      processTacticsListing( rest takeWhile { _ != endTacticsListing }, optionString, interp )
      processLines( rest dropWhile { _ != endTacticsListing } drop 1, interp )
    case `beginTacticsOutput` #:: rest =>
      processLines( rest dropWhile { _ != endTacticsOutput } drop 1, interp )
    case line #:: rest =>
      println( line )
      processLines( rest, interp )
    case Stream() =>
  }

  def main( args: Array[String] ) = {
    val Array( inFile ) = args
    processLines( read.lines( Path( inFile, pwd ) ).toStream, mkInterp() )
  }

}
