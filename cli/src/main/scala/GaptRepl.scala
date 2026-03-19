package gapt.cli

import gapt.formats.ClasspathInputFile
import dotty.tools.repl._
import java.io.PrintStream
import org.jline.reader.Completer
import scala.jdk.CollectionConverters._
import dotty.tools.dotc.core.Contexts.Context
import org.jline.reader.EndOfFileException
import org.jline.reader.UserInterruptException
import scala.annotation.tailrec
import org.jline.reader.Candidate
import org.jline.reader.LineReader
import dotty.tools.dotc.printing.SyntaxHighlighting
import dotty.tools.repl.Rendering.showUser

case class GaptRepl() {

  class GaptTerminal extends JLineTerminal {
    override protected def promptStr: String = "gapt"
  }

  class GaptReplDriver(out: PrintStream = Console.out) extends ReplDriver(Array(
        "-usejavacp",
        "-feature",
        "-deprecation",
        "-language:postfixOps",
        "-language:implicitConversions"
      )) {

    override def runUntilQuit(using initialState: State = initialState)(): State = {
      // Most of this implementation is copied from the scala compiler version 3.3.6
      // (see https://github.com/scala/scala3/blob/release-3.3.6/compiler/src/dotty/tools/repl/ReplDriver.scala)
      // This is necessary since the ReplDriver implementation is not extensible
      // enough to allow setting the prompt string and welcome message.
      // However, this means that future changes in the scala compiler might have to be incorporated here.

      // These first two lines are new
      val terminal = new GaptTerminal
      out.println(welcomeMessage)

      // The rest is copied from the implementation linked above

      /** Blockingly read a line, getting back a parse result */
      def readLine()(using state: State): ParseResult = {
        given Context = state.context
        val completer: Completer = { (lineReader, line, candidates) =>
          def makeCandidate(label: String) = {
            new Candidate(
              /* value    = */ label,
              /* displ    = */ stripBackTicks(label), // displayed value
              /* group    = */ null, // can be used to group completions together
              /* descr    = */ null, // TODO use for documentation?
              /* suffix   = */ null,
              /* key      = */ null,
              /* complete = */ false // if true adds space when completing
            )
          }
          val comps = completionsWithSignatures(line.cursor, line.line, state)
          candidates.addAll(comps.map(_.label).distinct.map(makeCandidate).asJava)
          val lineWord = line.word()
          comps.filter(c => c.label == lineWord && c.symbols.nonEmpty) match
            case Nil =>
            case exachMatches =>
              val terminal = lineReader.nn.getTerminal
              lineReader.callWidget(LineReader.CLEAR)
              terminal.writer.println()
              exachMatches.foreach: exact =>
                exact.symbols.foreach: sym =>
                  terminal.writer.println(SyntaxHighlighting.highlight(sym.showUser))
              lineReader.callWidget(LineReader.REDRAW_LINE)
              lineReader.callWidget(LineReader.REDISPLAY)
              terminal.flush()
        }

        try {
          val line = terminal.readLine(completer)
          ParseResult(line)
        } catch {
          case _: EndOfFileException |
              _: UserInterruptException => // Ctrl+D or Ctrl+C
            Quit
        }
      }

      @tailrec def loop(using state: State)(): State = {
        val res = readLine()
        if (res == Quit) state
        else loop(using interpret(res))()
      }

      try runBody { loop() }
      finally terminal.close()
    }

    private def stripBackTicks(label: String) =
      if label.startsWith("`") && label.endsWith("`") then
        label.drop(1).dropRight(1)
      else
        label
  }

  def run(): Unit =
    val repl = new GaptReplDriver
    val initialState = repl.initialState
    val state = repl.run(readPredefFile)(using initialState)
    repl.runUntilQuit(using state)()

  private def readPredefFile: String =
    ClasspathInputFile(predefFileName).read
}
