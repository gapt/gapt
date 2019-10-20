package gapt.doc

import java.io.{ ByteArrayOutputStream, PrintStream, PrintWriter, Writer }
import java.nio.ByteBuffer
import java.nio.charset.Charset

import ammonite.ops._
import gapt.cli
import gapt.formats.ClasspathInputFile

import scala.collection.parallel.CollectionConverters._
import scala.tools.nsc.Settings
import scala.tools.nsc.interpreter.IMain
import scala.tools.nsc.interpreter.shell.{ ReplReporterImpl, ShellConfig }
import scala.util.matching.Regex

case class Document( sections: Vector[Section] ) {
  override def toString = sections.mkString
}

case class Section( chunks: Vector[Chunk] ) {
  override def toString = chunks.mkString
}

sealed trait Chunk
case class Text( text: String ) extends Chunk {
  override def toString = text
}
case class CliListing(
    condition: Option[String],
    commands:  Vector[( String, String )] ) extends Chunk {
  override def toString = {
    "\\begin{clilisting}" +
      ( condition match { case Some( cond ) => s"[$cond]" case None => "" } ) +
      "\n" +
      commands.map {
        case ( input, output ) =>
          s"gapt> $input\n$output\n"
      }.mkString +
      "\\end{clilisting}\n"
  }
}
case class TacticsListing(
    options: Vector[String],
    input:   String,
    output:  String ) extends Chunk {
  override def toString = {
    "\\begin{tacticslisting}" +
      ( if ( options.nonEmpty ) s"[${options.mkString( "," )}]" else "" ) +
      "\n" +
      input +
      "\\end{tacticslisting}\n" +
      "\\begin{tacticsoutput}\n" +
      output +
      "\\end{tacticsoutput}\n"
  }
}

class WriterOutputStream( writer: Writer, charset: Charset = Charset.forName( "UTF-8" ) )
  extends ByteArrayOutputStream {
  override def flush(): Unit = {
    writer.write( charset.decode( ByteBuffer.wrap( toByteArray ) ).toString )
    reset()
  }
}

class ResultHolder( var result: Any )
class CommandEvaluator {
  val settings = new Settings
  settings.usejavacp.value = true

  sys.props( "scala.shell.prompt" ) = "\ngapt> "

  val out = new StringBuilder
  val outWriter = new Writer() {
    override def flush() = {}
    override def write( cbuf: Array[Char], off: Int, len: Int ) =
      out.append( new String( cbuf, off, len ) )
    override def close() = {}
  }
  val outPrintStream = new PrintStream( new WriterOutputStream( outWriter ), true )

  // toString() of lambdas includes the hashcode
  val lambdaRegex = """\b[A-Za-z.0-9$]+\$\$\$?Lambda\$\d+/(\d+|0x[0-9a-f]+)@[0-9a-f]+""".r
  // "... 82 elided" is different between compile server and my machine
  val elidedRegex = """... \d+ elided""".r
  def getOutput: String = {
    var o = out.result()
    o = lambdaRegex.replaceAllIn( o, "<function>" )
    o = elidedRegex.replaceAllIn( o, "... elided" )
    o
  }

  val interpreter = new IMain(
    settings,
    new ReplReporterImpl(
      config = ShellConfig( settings ),
      settings = settings,
      writer = new PrintWriter( outWriter ) ) )

  interpreter.interpret( ClasspathInputFile( cli.predefFileName ).read )

  // don't open prooftool
  interpreter.interpret( "def prooftool[T: gapt.prooftool.ProoftoolViewable](x: T, name: String = \"\"): Unit = ()" )

  // don't open help
  interpreter.interpret( "def help(x: Any*): Unit = ()" )

  def runCommand( cmd: String ): String = {
    out.clear()
    Console.withOut( outPrintStream )( interpreter.interpret( cmd ) )
    getOutput
  }

  def incrementCounter(): Unit =
    runCommand( "true" )

  def evalCodeInInterp( code: String ): Any = {
    val resultHolder = new ResultHolder( null )
    val varName = "$evalCodeSnippetsInLatex_result"
    interpreter.bind( varName, resultHolder )
    interpreter.interpret( s"$varName.result = ($code)" )
    resultHolder.result
  }
}

object evaluate {
  def apply( doc: Document ): Document = {
    Document( doc.sections.par.map( apply ).seq )
  }

  def apply( section: Section ): Section = {
    val evaluator = new CommandEvaluator
    Section( section.chunks.map( apply( _, evaluator ) ) )
  }

  val assignment = """val\s+\w+\s+=.*""".r
  def apply( chunk: Chunk, evaluator: CommandEvaluator ): Chunk =
    chunk match {
      case Text( text ) => Text( text )
      case CliListing( Some( cond ), commands ) if !evaluator.evalCodeInInterp( cond ).asInstanceOf[Boolean] =>
        Console.err.println( s"Skipping snippet because condition failed: $cond" )
        commands.foreach {
          case ( assignment(), _ ) =>
          case _                   => evaluator.incrementCounter()
        }
        chunk
      case CliListing( cond, commands ) =>
        CliListing( cond, commands.map { case ( in, _ ) => ( in, evaluator.runCommand( in ) ) } )
      case TacticsListing( options, input, _ ) =>
        var code = input
        if ( !options.contains( "nosig" ) && !options.contains( "bare" ) ) code = s"""
          ctx += Sort("i")
          ctx += hoc"P: i>o"
          ctx += hoc"Q: i>o"
          ctx += hoc"I: i>o"
          ctx += hoc"a: i"
          ctx += hoc"b: i"
          ctx += hoc"0: i"
          ctx += hoc"1: i"
          ctx += hoc"f: i>i"
          ctx += hoc"A: o"
          ctx += hoc"B: o"
          $code
        """
        if ( !options.contains( "bare" ) ) code = s"""
          new TacticsProof {
            $code
          }
        """
        code = s"""
          val () = {
            import gapt.proofs.gaptic._
            import gapt.formats.babel._
            $code
            ()
          }
        """
        TacticsListing( options, input, evaluator.runCommand( code ) )
    }
}

object parse {
  def apply( contents: String ): Document =
    ( document( contents.linesIterator.toList ): @unchecked ) match {
      case Some( ( doc, Nil ) ) => doc
    }

  trait Parser[+A] {
    def apply( lines: List[String] ): Option[( A, List[String] )]

    def * : Parser[Vector[A]] = {
      val builder = Vector.newBuilder[A]
      def go( lines: List[String] ): Some[( Vector[A], List[String] )] =
        apply( lines ) match {
          case Some( ( a, ls ) ) =>
            builder += a
            go( ls )
          case None =>
            Some( ( builder.result(), lines ) )
        }
      go
    }
    def flatMap[B]( f: A => Parser[B] ): Parser[B] =
      lines => apply( lines ) match {
        case Some( ( a, lines2 ) ) => f( a )( lines2 )
        case None                  => None
      }
    def map[B]( f: A => B ): Parser[B] =
      flatMap( a => pure( f( a ) ) )
    def |[B >: A]( p: Parser[B] ): Parser[B] =
      lines => apply( lines ) match {
        case None => p( lines )
        case res  => res
      }
    def ? : Parser[Option[A]] =
      map( Some( _ ) ) | pure( None )
    def filter( pred: A => Boolean ): Parser[A] =
      lines => apply( lines ) match {
        case res @ Some( ( a, _ ) ) if pred( a ) => res
        case _                                   => None
      }
    def withFilter( pred: A => Boolean ): Parser[A] = filter( pred )
  }
  def pure[A]( a: A ): Parser[A] = lines => Some( ( a, lines ) )
  def sat( pred: String => Boolean ): Parser[String] = {
    case line :: lines if pred( line ) => Some( ( line, lines ) )
    case _                             => None
  }
  def regex0( r: Regex ): Parser[String] =
    sat( s => r.pattern.matcher( s ).matches() )
  def regex1( r: Regex ): Parser[Option[String]] = {
    case r( a ) :: lines => Some( ( Option( a ), lines ) )
    case _               => None
  }

  def linesWhile( pred: String => Boolean ): Parser[String] =
    sat( pred ).*.map( _.map( _ + "\n" ).mkString )

  val beginSection = """\s*\\section\{.*""".r
  val cliInputLine = """\s*gapt> (.*)""".r
  val beginCliListing = """\\begin\{clilisting\}(?:\[(.*)\])?""".r
  val endCliListing = """\end{clilisting}"""
  val beginTacticsListing = """\\begin\{tacticslisting\}(?:\[(.*)\])?""".r
  val endTacticsListing = """\end{tacticslisting}"""
  val beginTacticsOutput = """\begin{tacticsoutput}"""
  val endTacticsOutput = """\end{tacticsoutput}"""

  def document: Parser[Document] =
    section.*.map( Document )

  def section: Parser[Section] =
    for {
      headline <- sectionLine.?
      chunks <- ( cliListing | tacticsListing | textLine ).*
      if headline.nonEmpty || chunks.nonEmpty
    } yield Section( headline.toVector ++ chunks )

  def sectionLine: Parser[Text] =
    sat( l => beginSection.pattern.matcher( l ).matches() ).map( l => Text( l + "\n" ) )
  def textLine: Parser[Text] =
    sat( l => !beginSection.pattern.matcher( l ).matches() ).map( l => Text( l + "\n" ) )

  def tacticsListing: Parser[TacticsListing] =
    for {
      opts <- regex1( beginTacticsListing )
      input <- linesWhile( _ != endTacticsListing )
      _ <- sat( _ == endTacticsListing ).?
      _ <- sat( _ == beginTacticsOutput ).?
      output <- linesWhile( _ != endTacticsOutput )
      _ <- sat( _ == endTacticsOutput ).?
    } yield TacticsListing(
      opts.map( _.split( "," ).toVector ).getOrElse( Vector() ),
      input,
      output )

  def cliListing: Parser[CliListing] =
    for {
      cond <- regex1( beginCliListing )
      commands <- cliListingCommand.*
      _ <- sat( _ == endCliListing ).?
    } yield CliListing( cond, commands )
  def cliListingCommand: Parser[( String, String )] =
    for {
      input <- regex1( cliInputLine )
      output <- linesWhile {
        case cliInputLine( _ ) => false
        case `endCliListing`   => false
        case _                 => true
      }
    } yield ( input.get, if ( output.endsWith( "\n" ) ) output.dropRight( 1 ) else output )
}

object evalCodeSnippets {

  def main( args: Array[String] ) = {
    val Array( inFile ) = args
    val in = read( Path( inFile, pwd ) )
    val inDoc = parse( in )
    val evaledDoc = evaluate( inDoc )
    print( evaledDoc )
  }

}
