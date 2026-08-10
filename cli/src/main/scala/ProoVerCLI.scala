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
    val szsStatus = Await.result(future, 28.seconds)
    Console.out.println(szsStatus.statusLine)
  } catch {
    case e: TimeoutException => Console.out.println(SzsStatus.Timeout.statusLine)
    case e                   => Console.out.println(SzsStatus.Unknown(e).statusLine)
  }
}
