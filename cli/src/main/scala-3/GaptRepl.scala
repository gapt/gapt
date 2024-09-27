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

case class GaptRepl() {

  class GaptTerminal extends JLineTerminal {
    override protected def promptStr: String = "gapt"
  }

  class GaptReplDriver(out: PrintStream = Console.out, classLoader: Option[ClassLoader] = None) extends ReplDriver(Array(
        "-usejavacp",
        "-feature",
        "-deprecation",
        "-language:postfixOps",
        "-language:implicitConversions"
      )) {

    override def runUntilQuit(using initialState: State)(): State = {
      // Most of this implementation is copied from the scala compiler version 3.3.1
      // (see https://github.com/scala/scala3/blob/release-3.3.1/compiler/src/dotty/tools/repl/ReplDriver.scala)
      // This is necessary since the ReplDriver implementation is not extensible
      // enough to allow setting the prompt string and welcome message.
      // However, this means that future changes in the scala compiler might have to be incorporated here.

      // These first two lines are new
      val terminal = new GaptTerminal
      out.println(welcomeMessage)

      // The rest is copied from the implementation linked above

      /** Blockingly read a line, getting back a parse result */
      def readLine()(using state: State): ParseResult = {
        val completer: Completer = { (_, line, candidates) =>
          val comps = completions(line.cursor, line.line, state)
          candidates.addAll(comps.asJava)
        }
        given Context = state.context
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
  }

  def run(): Unit =
    val repl = new GaptReplDriver
    val state = repl.runQuietly(readPredefFile)(using repl.initialState)
    repl.runUntilQuit(using state)()

  private def readPredefFile: String =
    ClasspathInputFile(predefFileName).read
}
