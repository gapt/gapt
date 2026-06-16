package gapt.testing

import os.{walk, pwd}
import gapt.utils.runProcess
import gapt.formats.tptp.TptpProofParser
import gapt.formats.InputFile
import gapt.utils.withTimeout
import scala.concurrent.duration._
import gapt.utils.TimeOutException
import scala.collection.parallel.CollectionConverters._
import os.Path
import java.io.IOException

case class Prover(name: String, fn: Path => String)

val vampire = Prover(
  "vampire",
  { p =>
    runProcess(
      Seq(
        "vampire",
        "--proof",
        "tptp",
        "--include",
        p.toString
      ),
      cwd = pwd / "testing" / "TPTP" / "problems"
    )
  }
)

val eprover = Prover(
  "eprover",
  { p =>
    runProcess(
      Seq("eprover", "-p", "--tptp3-format"),
      os.read(p),
      cwd = pwd / "testing" / "TPTP" / "problems"
    )
  }
)

val metis = Prover(
  "metis",
  { p =>
    runProcess(
      Seq("metis", "--show", "proof", p.toString),
      cwd = pwd / "testing" / "TPTP" / "problems"
    )
  }
)

@main def generateTstpFiles(): Unit = {
  val tptpProblems = walk(pwd / "testing" / "TPTP" / "problems").filter(p => p.ext == "p").toList
  println(s"got ${tptpProblems.size} problems")
  val provers = Seq(vampire, eprover, metis)
  val timeout = 5.seconds
  val configurations =
    for
      problemPath <- tptpProblems
      prover <- provers
    yield (prover, problemPath)

  configurations.par.foreach { (prover, problem) =>
    try {
      System.out.println(s"running ${prover.name} on $problem")
      val output = withTimeout(timeout) {
        prover.fn(problem)
      }
      System.out.println(s"got result from ${prover.name} on $problem")
      val inputRelativePath = problem.relativeTo(pwd / "testing" / "TPTP" / "problems" / "Problems")
      val outputPath = pwd / "testing" / "TSTP" / "Solutions" / inputRelativePath / s"${prover.name}.tstp"
      os.write.over(outputPath, output, createFolders = true)
      System.out.println(s"wrote ${prover.name} result to $outputPath")
    } catch {
      case _: TimeOutException => {
        System.err.println(s"${prover.name} timed out after ${timeout} on $problem")
      }
      case e: Exception => {
        System.err.println(s"${prover.name} failed on $problem: $e")
      }
    }
  }
}
