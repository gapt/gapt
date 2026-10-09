package gapt.testing

import scala.sys.process.{Process, ProcessBuilder}
import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Await
import scala.concurrent.duration._
import java.util.concurrent.TimeoutException
import scala.util.Random
import scala.sys.process.ProcessLogger

enum DerivationStatus {
  case Correct
  case Incorrect
  case Removed
}
enum CheckerResult {
  case VerifiedGood
  case VerifiedBad
  case Unknown
  case SignaledTimeout
  case UnsignaledTimeout
  case Crashed
  case InvalidOutput
}

@main
def simulateProoVerCompetition() = {
  val timeout = 30.seconds
  val targetPath = os.Path("target", os.pwd)
  if !os.exists(targetPath) then {
    Console.err.println("could not find target directory")
    sys.exit(1)
  }

  val prooVerDistNoTestProcess = Process(Seq("sbt", "prooVerDistNoTest")).run()
  if prooVerDistNoTestProcess.exitValue() != 0 then {
    Console.err.println("failed to build checker")
    sys.exit(1)
  }

  Console.println("unzipping checker...")
  val unzipProcess = Process(Seq("unzip", "-o", "gapt-ProoVer.zip", "-d", "ProoVer"), targetPath.toIO).run()
  if unzipProcess.exitValue() != 0 then {
    Console.err.println("could unzip gapt-ProoVer.zip into ProoVer")
    sys.exit(1)
  }

  if !os.exists(targetPath / "ProoVer" / "gapt-check") then {
    Console.err.println("could not find gapt-check")
    sys.exit(1)
  }

  val checkerPwd = os.Path("target/ProoVer", os.pwd)
  val checkerPath = checkerPwd / "gapt-check"

  val derivationsPath = os.Path("tests/src/test/resources/ProoVerCompetition/ProoVer2026", os.pwd)
  val derivationPaths = os.list(derivationsPath).filter(_.ext == "s")

  def buildCheckerProcess(derivationPath: os.Path): ProcessBuilder = {
    Process(Seq(checkerPath.toString, derivationPath.toString), checkerPwd.toIO)
  }

  val results = Random.shuffle(derivationPaths).map { derivationPath =>
    Console.println(s"Running checker on ${derivationPath.baseName}")

    val derivationStatus =
      if derivationPath.baseName.startsWith("claimed_correct_")
        || derivationPath.baseName.startsWith("correct_")
      then {
        DerivationStatus.Correct
      } else if derivationPath.baseName.startsWith("claimed_incorrect_")
        || derivationPath.baseName.startsWith("incorrect_")
      then {
        DerivationStatus.Incorrect
      } else if derivationPath.baseName.startsWith("removed_")
      then {
        DerivationStatus.Removed
      } else {
        Console.println(s"Unknown derivation status for ${derivationPath.baseName}")
        sys.exit(1)
      }
    val (checkerProcess, checkerFuture) = {
      val processBuilder = buildCheckerProcess(derivationPath)
      var checkerOutput: Option[String] = None
      val checkerProcess = processBuilder.run(
        ProcessLogger(line => checkerOutput = Some(line), line => Console.err.println(line))
      )
      (
        checkerProcess,
        Future {
          try {
            val checkerExitValue = checkerProcess.exitValue()
            if checkerExitValue != 0 then {
              throw new Exception(s"checker exited with code $checkerExitValue")
            }

            val checkerStdOut = checkerOutput.getOrElse {
              throw new Exception("checker did not produce any output")
            }

            if checkerStdOut.startsWith("% SZS status VerifiedGood") then {
              CheckerResult.VerifiedGood
            } else if checkerStdOut.startsWith("% SZS status VerifiedBad") then {
              CheckerResult.VerifiedBad
            } else if checkerStdOut.startsWith("% SZS status Unknown") then {
              CheckerResult.Unknown
            } else if checkerStdOut.startsWith("% SZS status Timeout") then {
              CheckerResult.SignaledTimeout
            } else {
              CheckerResult.InvalidOutput
            }
          } catch {
            case e => {
              Console.err.println(s"failed to run checker on $derivationPath: ${e.getMessage}")
              CheckerResult.Crashed
            }
          }
        }
      )
    }

    val timeStart = System.nanoTime()
    val checkerResult =
      try {
        Await.result(checkerFuture, timeout)
      } catch {
        case _: TimeoutException => CheckerResult.UnsignaledTimeout
      } finally {
        checkerProcess.destroy()
      }
    val timeEnd = System.nanoTime()
    val timeElapsed = timeEnd - timeStart
    val duration = Duration(timeElapsed, NANOSECONDS)

    val score = (derivationStatus, checkerResult) match {
      case (DerivationStatus.Correct, CheckerResult.VerifiedGood)   => 1
      case (DerivationStatus.Incorrect, CheckerResult.VerifiedBad)  => 2
      case (DerivationStatus.Correct, CheckerResult.VerifiedBad)    => -1
      case (DerivationStatus.Incorrect, CheckerResult.VerifiedGood) => -10
      case _                                                        => 0
    }

    val record = (derivation = derivationPath, derivationStatus = derivationStatus, checkerResult = checkerResult, score = score, duration = duration)

    Console.println(s"${scoreMark(record.score)} $record")
    record
  }

  printResults(results)
}

type CompetitionResult = (derivation: os.Path, derivationStatus: DerivationStatus, checkerResult: CheckerResult, score: Int, duration: FiniteDuration)

def printResults(results: IndexedSeq[CompetitionResult]): Unit = {
  Console.println("\nRESULTS")
  results.sortBy(r => r.derivation.baseName.split("_").last).foreach(printResult)
  printResultSummary(results)
}

private def printResult(result: CompetitionResult): Unit = {
  val derivationStatusText = result.derivationStatus match {
    case DerivationStatus.Correct   => "😇"
    case DerivationStatus.Incorrect => "😈"
    case DerivationStatus.Removed   => "😶"
  }
  val padding = " " * (30 - result.derivation.baseName.length)
  Console.println(s"${result.derivation.baseName}$padding ${derivationStatusText}: ${scoreMark(result.score)} ${result.checkerResult}, score: ${result.score}, time: ${formatDuration(result.duration)}")
}

private def printResultSummary(results: IndexedSeq[CompetitionResult]): Unit = {
  val numberOfTests = results.length
  val maxScore =
    results.count(_.derivationStatus == DerivationStatus.Correct)
      + results.count(_.derivationStatus == DerivationStatus.Incorrect) * 2
  val totalScore = results.map(_.score).sum
  val totalDuration = results.map(_.duration).foldLeft(Duration.Zero)(_ + _)
  Console.println(s"Number of tests:         $numberOfTests")
  Console.println(s"Total score:             $totalScore / $maxScore")
  Console.println(s"Total duration:          ${formatDuration(totalDuration)}")
  Console.println(s"😇 VerifiedGood:         ${results.count(r => r.derivationStatus == DerivationStatus.Correct && r.checkerResult == CheckerResult.VerifiedGood)}")
  Console.println(s"😈 VerifiedBad:          ${results.count(r => r.derivationStatus == DerivationStatus.Incorrect && r.checkerResult == CheckerResult.VerifiedBad)}")
  Console.println(s"😇 VerifiedBad:          ${results.count(r => r.derivationStatus == DerivationStatus.Correct && r.checkerResult == CheckerResult.VerifiedBad)}")
  Console.println(s"😈 VerifiedGood:         ${results.count(r => r.derivationStatus == DerivationStatus.Incorrect && r.checkerResult == CheckerResult.VerifiedGood)}")
  Console.println(s"😇 non-timeout unknowns: ${results.count(r => r.derivationStatus == DerivationStatus.Correct && r.checkerResult == CheckerResult.Unknown)}")
  Console.println(s"😈 non-timeout unknowns: ${results.count(r => r.derivationStatus == DerivationStatus.Incorrect && r.checkerResult == CheckerResult.Unknown)}")
  Console.println(s"😇 timeout:              ${results.count(r => r.derivationStatus == DerivationStatus.Correct && (r.checkerResult == CheckerResult.UnsignaledTimeout || r.checkerResult == CheckerResult.SignaledTimeout))}")
  Console.println(s"😈 timeout:              ${results.count(r => r.derivationStatus == DerivationStatus.Incorrect && (r.checkerResult == CheckerResult.UnsignaledTimeout || r.checkerResult == CheckerResult.SignaledTimeout))}")
  Console.println(s"💥 Crashed:              ${results.count(_.checkerResult == CheckerResult.Crashed)}")
  Console.println(s"⚠️  Invalid output:       ${results.count(_.checkerResult == CheckerResult.InvalidOutput)}")
}

def scoreMark(score: Int) = {
  val red = "\u001b[31m"
  val green = "\u001b[32m"
  val purple = "\u001b[35m"
  val reset = "\u001b[0m"

  if score > 0 then s"${green}✓${reset}"
  else if (score < 0) then s"${red}✗${reset}"
  else s"${purple}○${reset}"
}

def formatDuration(d: Duration): String = {
  val millis = d.toMillis
  val seconds = millis / 1000
  val remainingMillis = millis % 1000

  s"${seconds}s ${remainingMillis}ms"
}
