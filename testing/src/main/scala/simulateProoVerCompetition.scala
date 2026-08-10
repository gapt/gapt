package gapt.testing

import scala.sys.process.{Process, ProcessBuilder}
import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Await
import scala.concurrent.duration._
import java.util.concurrent.TimeoutException
import scala.util.Random
import scala.sys.process.ProcessLogger

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
    Console.err.println("failed to build solver")
    sys.exit(1)
  }

  Console.println("unzipping solver...")
  val unzipProcess = Process(Seq("unzip", "-o", "gapt-ProoVer.zip", "-d", "ProoVer"), targetPath.toIO).run()
  if unzipProcess.exitValue() != 0 then {
    Console.err.println("could unzip gapt-ProoVer.zip into ProoVer")
    sys.exit(1)
  }

  if !os.exists(targetPath / "ProoVer" / "gapt-check") then {
    Console.err.println("could not find gapt-check")
    sys.exit(1)
  }

  val solverPwd = os.Path("target/ProoVer", os.pwd)
  val solverPath = solverPwd / "gapt-check"

  val derivationsPath = os.Path("tests/src/test/resources/ProoVer_competition/Proofs/ProoVer2026", os.pwd)
  val derivationPaths = os.list(derivationsPath).filter(_.ext == "s")

  def buildSolverProcess(derivationPath: os.Path): ProcessBuilder = {
    Process(Seq(solverPath.toString, derivationPath.toString), solverPwd.toIO)
  }

  enum DerivationStatus {
    case Correct
    case Incorrect
  }
  enum SolverResult {
    case VerifiedGood
    case VerifiedBad
    case Unknown
    case SignaledTimeout
    case UnsignaledTimeout
    case Crashed
    case InvalidOutput
  }
  val results = Random.shuffle(derivationPaths).map { derivationPath =>
    Console.println(s"Running solver on ${derivationPath.baseName}")

    val derivationStatus =
      if derivationPath.baseName.startsWith("claimed_correct_")
        || derivationPath.baseName.startsWith("correct_")
      then {
        DerivationStatus.Correct
      } else if derivationPath.baseName.startsWith("claimed_incorrect_")
        || derivationPath.baseName.startsWith("incorrect_")
      then {
        DerivationStatus.Incorrect
      } else {
        Console.println(s"Unknown derivation status for ${derivationPath.baseName}")
        sys.exit(1)
      }
    val (solverProcess, solverFuture): (Process, Future[SolverResult]) = {
      val processBuilder = buildSolverProcess(derivationPath)
      var solverOutput: Option[String] = None
      val solverProcess = processBuilder.run(
        ProcessLogger(line => solverOutput = Some(line), line => Console.err.println(line))
      )
      (
        solverProcess,
        Future {
          try {
            val solverExitValue = solverProcess.exitValue()
            if solverExitValue != 0 then {
              throw new Exception(s"solver exited with code $solverExitValue")
            }

            val solverStdOut = solverOutput.getOrElse {
              throw new Exception("solver did not produce any output")
            }

            if solverStdOut.startsWith("% SZS status VerifiedGood") then {
              SolverResult.VerifiedGood
            } else if solverStdOut.startsWith("% SZS status VerifiedBad") then {
              SolverResult.VerifiedBad
            } else if solverStdOut.startsWith("% SZS status Unknown") then {
              SolverResult.Unknown
            } else if solverStdOut.startsWith("% SZS status Timeout") then {
              SolverResult.SignaledTimeout
            } else {
              SolverResult.InvalidOutput
            }
          } catch {
            case e => {
              Console.err.println(s"failed to run solver on $derivationPath: ${e.getMessage}")
              SolverResult.Crashed
            }
          }
        }
      )
    }

    val timeStart = System.nanoTime()
    val solverResult =
      try {
        Await.result(solverFuture, timeout)
      } catch {
        case _: TimeoutException => SolverResult.UnsignaledTimeout
      } finally {
        solverProcess.destroy()
      }
    val timeEnd = System.nanoTime()
    val timeElapsed = timeEnd - timeStart
    val duration = Duration(timeElapsed, NANOSECONDS)

    val score = (derivationStatus, solverResult) match {
      case (DerivationStatus.Correct, SolverResult.VerifiedGood)   => 1
      case (DerivationStatus.Incorrect, SolverResult.VerifiedBad)  => 2
      case (DerivationStatus.Correct, SolverResult.VerifiedBad)    => -1
      case (DerivationStatus.Incorrect, SolverResult.VerifiedGood) => -10
      case _                                                       => 0
    }

    val record = (derivation = derivationPath, derivationStatus = derivationStatus, solverResult = solverResult, score = score, duration = duration)

    Console.println(s"${scoreMark(record.score)} $record")
    record
  }

  Console.println("\nRESULTS")
  results.sortBy(r => r.derivation.baseName.split("_").last).foreach { result =>
    val derivationStatusText = result.derivationStatus match {
      case DerivationStatus.Correct   => "😇"
      case DerivationStatus.Incorrect => "😈"
    }
    val padding = " " * (30 - result.derivation.baseName.length)
    Console.println(s"${result.derivation.baseName}$padding ${derivationStatusText}: ${scoreMark(result.score)} ${result.solverResult}, score: ${result.score}, time: ${formatDuration(result.duration)}")
  }

  val numberOfTests = results.length
  val maxScore =
    results.count(_.derivationStatus == DerivationStatus.Correct)
      + results.count(_.derivationStatus == DerivationStatus.Incorrect) * 2
  val totalScore = results.map(_.score).sum
  val totalDuration = results.map(_.duration).foldLeft(Duration.Zero)(_ + _)
  Console.println(s"Number of tests:         $numberOfTests")
  Console.println(s"Total score:             $totalScore / $maxScore")
  Console.println(s"Total duration:          ${formatDuration(totalDuration)}")
  Console.println(s"😇 VerifiedGood:         ${results.count(r => r.derivationStatus == DerivationStatus.Correct && r.solverResult == SolverResult.VerifiedGood)}")
  Console.println(s"😈 VerifiedBad:          ${results.count(r => r.derivationStatus == DerivationStatus.Incorrect && r.solverResult == SolverResult.VerifiedBad)}")
  Console.println(s"😇 VerifiedBad:          ${results.count(r => r.derivationStatus == DerivationStatus.Correct && r.solverResult == SolverResult.VerifiedBad)}")
  Console.println(s"😈 VerifiedGood:         ${results.count(r => r.derivationStatus == DerivationStatus.Incorrect && r.solverResult == SolverResult.VerifiedGood)}")
  Console.println(s"😇 non-timeout unknowns: ${results.count(r => r.derivationStatus == DerivationStatus.Correct && r.solverResult == SolverResult.Unknown)}")
  Console.println(s"😈 non-timeout unknowns: ${results.count(r => r.derivationStatus == DerivationStatus.Incorrect && r.solverResult == SolverResult.Unknown)}")
  Console.println(s"😇 timeout:              ${results.count(r => r.derivationStatus == DerivationStatus.Correct && (r.solverResult == SolverResult.UnsignaledTimeout || r.solverResult == SolverResult.SignaledTimeout))}")
  Console.println(s"😈 timeout:              ${results.count(r => r.derivationStatus == DerivationStatus.Incorrect && (r.solverResult == SolverResult.UnsignaledTimeout || r.solverResult == SolverResult.SignaledTimeout))}")
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
