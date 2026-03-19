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
      // Most of this implementation is copied from the scala repl version 3.8.2
      // (see https://github.com/scala/scala3/blob/release-3.8.2/repl/src/dotty/tools/repl/ReplDriver.scala)
      // This is necessary since the ReplDriver implementation is not extensible
      // enough to allow setting the prompt string and welcome message.
      // However, this means that future changes in the scala repl might have to be incorporated here.

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
          val comps = completions(line.cursor, line.line, state)
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
          case _: EndOfFileException => // Ctrl+D
            Quit
          case _: UserInterruptException => // Ctrl+C at prompt - clear and continue
            SigKill
        }
      }

      @tailrec def loop(using state: State)(): State = {
        val res = readLine()
        if (res == Quit) state
        else if (res == SigKill) loop(using state)()
        else {
          var firstCtrlCEntered = false
          val thread = Thread.currentThread()

          ReplBytecodeInstrumentation.setStopFlag(replClassLoader(using state.context), false)

          val newState = terminal.withMonitoringCtrlC(
            handler = () =>
              if (!firstCtrlCEntered) {
                firstCtrlCEntered = true
                ReplBytecodeInstrumentation.setStopFlag(replClassLoader(using state.context), true)
                thread.interrupt()
                out.println("\nAttempting to interrupt running REPL command")
              } else {
                out.println("\nTerminating REPL Process...")
                System.exit(130)
              }
          ) {
            interpret(res)
          }

          loop(using newState)()
        }
      }

      try runBody { loop() }
      finally terminal.close()
    }

    private def stripBackTicks(label: String) =
      if label.startsWith("`") && label.endsWith("`") then
        label.drop(1).dropRight(1)
      else
        label

    // ReplDriver uses Rendering.classLoader(), but that helper is package-private.
    // Keep a local copy of the 3.8.2 logic here so the interrupt instrumentation
    // behaves like upstream while preserving our custom prompt/welcome handling.
    private def replClassLoader(using ctx: Context): ClassLoader =
      if (rendering.myClassLoader != null) rendering.myClassLoader
      else {
        val compilerClasspath = ctx.platform.classPath(using ctx).asURLs
        val baseClassLoader = ClassLoader.getSystemClassLoader.getParent
        val parent = new java.net.URLClassLoader(compilerClasspath.toArray, baseClassLoader)

        rendering.myClassLoader = new AbstractFileClassLoader(
          ctx.settings.outputDir.value,
          parent,
          AbstractFileClassLoader.InterruptInstrumentation.fromString(
            ctx.settings.XreplInterruptInstrumentation.value
          )
        )
        rendering.myClassLoader
      }
  }

  def run(): Unit =
    val repl = new GaptReplDriver
    val initialState = repl.initialState
    val state = repl.run(readPredefFile)(using initialState)
    repl.runUntilQuit(using state)()

  private def readPredefFile: String =
    ClasspathInputFile(predefFileName).read
}
