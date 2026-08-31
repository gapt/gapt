package gapt.cli

import gapt.formats.tptp.check._
import gapt.formats.OnDiskInputFile
import scala.concurrent.Future
import scala.concurrent.Await
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import java.util.concurrent.TimeoutException
import gapt.utils.LogHandler.VerbosityLevel
import gapt.utils.LogHandler

val usage = """
|./gapt-check <PROOF>
|
|Checks the correctness of a given proof.
|PROOF is a path to a TSTP proof file""".stripMargin.strip

class ProoVerLogHandler extends LogHandler {
  override def timeBegin(domain: String, verbosity: VerbosityLevel, key: String): Unit = {
    message(domain, verbosity, s"start $key")
  }
  override def message(domain: String, verbosity: VerbosityLevel, msg: => Any): Unit = {
    if domain.startsWith("time.") then
      Console.err.println(s"[$domain] $msg")
  }
}

@main
def prooVerCLI(args: String*): Unit = LogHandler.use(ProoVerLogHandler()) {
  val szsStatus =
    try {
      val future = Future {
        val input = args match {
          case Seq() => {
            Console.err.println(usage)
            sys.exit(1)
          }
          case Seq("--help") => {
            Console.out.println(usage)
            sys.exit(0)
          }
          case Seq(file) => file
        }

        val path = os.Path(input, os.pwd)
        if !os.exists(path) then {
          Console.err.println(s"file not found: $path")
          sys.exit(1)
        }

        checkTstpDerivation(OnDiskInputFile(path))
      }

      Await.result(future, 28.seconds)
    } catch {
      case e: TimeoutException => SzsStatus.Timeout
      case e                   => SzsStatus.Unknown(UnexpectedException(e))
    }
  Console.out.println(szsStatus.statusLine)
}
