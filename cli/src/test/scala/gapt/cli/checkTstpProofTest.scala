package gapt.cli

import org.specs2.Specification
import org.specs2.execute.Result
import org.specs2.specification.BeforeAll
import org.specs2.specification.core.Execution
import org.specs2.specification.core.Fragment
import org.specs2.specification.core.Fragments
import org.specs2.specification.core.SpecStructure

import os.Path
import scala.sys.process._

class checkTstpProofTest extends Specification with BeforeAll {
  private val usageText =
    """
      |check-proof <PROOF>
      |
      |Checks the correctness of a given proof.
      |PROOF is a path to a TSTP proof file""".stripMargin.strip

  trait Cwd { def path: Path }
  object RepoRoot extends Cwd { def path: Path = os.pwd / os.up }
  object ProoverCompetitionRoot extends Cwd {
    def path: Path = RepoRoot.path / "tests" / "src" / "test" / "resources" / "proover_competition"
  }
  val checkTstpProofJarPath = RepoRoot.path / "cli" / "target" / "check-tstp-proof.jar"

  private def assertExistsProofChecker(): Unit = {
    assert(os.exists(checkTstpProofJarPath))
  }

  private def proofCheckerProcess(args: String*)(using cwd: Cwd): ProcessBuilder =
    Process(
      Seq("java", "-jar", checkTstpProofJarPath.toString) ++ args,
      cwd.path.toIO
    )

  private def runWithExitCodeStdoutStderr(pb: ProcessBuilder): (Int, String, String) = {
    val stdout = scala.collection.mutable.ListBuffer[String]()
    val stderr = scala.collection.mutable.ListBuffer[String]()
    val process = pb.run(
      ProcessLogger(outLine => stdout += outLine, errLine => stderr += errLine)
    )
    val exitCode = process.exitValue()
    (exitCode, stdout.mkString("\n"), stderr.mkString("\n"))
  }

  extension (pb: ProcessBuilder)
    private def !!! : (Int, String, String) = runWithExitCodeStdoutStderr(pb)

  override def beforeAll(): Unit = assertExistsProofChecker()

  def is: SpecStructure = {
    given cwd: Cwd = ProoverCompetitionRoot

    def noInputFile: Result = {
      val (exitCode, _, _) = proofCheckerProcess().!!!
      exitCode must beGreaterThan(0)
    }

    def help: Result = {
      val (exitCode, _, _) = proofCheckerProcess("--help").!!!
      exitCode must_== 0
    }

    def usageOnNoInputFile: Result = {
      val (_, _, stderr) = proofCheckerProcess().!!!
      stderr must startWith(usageText)
    }

    def usageOnHelp: Result = {
      val (_, stdout, _) = proofCheckerProcess("--help").!!!
      stdout must startWith(usageText)
    }

    def nonExistentPath: Result = {
      val (exitCode, stdout, stderr) =
        proofCheckerProcess("./proofs/non_existing_file.p").!!!

      (exitCode must beGreaterThan(0)) and
        (stdout must beEmpty) and
        (stderr must startWith("file not found"))
    }

    def relativePaths: Result = {
      val (exitCode, _, _) =
        proofCheckerProcess("./proofs/correct/example1_c_proof.p").!!!

      exitCode must_== 0
    }

    def absolutePaths: Result = {
      val (exitCode, _, _) =
        proofCheckerProcess(s"${cwd.path}/proofs/correct/example1_c_proof.p").!!!

      exitCode must_== 0
    }

    def verifyCorrect(example: Path): Result = {
      val (exitCode, stdout, _) =
        proofCheckerProcess(example.toString).!!!

      (exitCode must_== 0) and
        (stdout must_== "%SZS status Verified")
    }

    def failVerification(example: Path): Result = {
      val (exitCode, stdout, _) =
        proofCheckerProcess(example.toString).!!!

      (exitCode must_== 0) and
        (stdout must_== "%SZS status FailedVerified")
    }

    def foreachPath(directory: Path)(f: Path => Fragment): Fragments = {
      val paths = os.list(directory)
      Fragments.foreach(paths) { path =>
        val fragment = f(path)
        val relativePath = path.relativeTo(ProoverCompetitionRoot.path)
        val pathFragment =
          if path.last.startsWith("skip") then
            fragment.setExecution(Execution.result(skipped(s"not testing $relativePath as it is marked skipped")))
          else fragment
        br ^ t ^ pathFragment ^ bt ^ br
      }
    }

    val correctProofs =
      foreachPath(ProoverCompetitionRoot.path / "proofs" / "correct") { example =>
        val relativePath = example.relativeTo(ProoverCompetitionRoot.path)
        s"verify $relativePath correctly" ! verifyCorrect(example)
      }

    val incorrectProofs =
      foreachPath(ProoverCompetitionRoot.path / "proofs" / "incorrect") { example =>
        val relativePath = example.relativeTo(ProoverCompetitionRoot.path)
        s"fail verification of $relativePath" ! failVerification(example)
      }

    s2"""
      |exit non-zero on no input file $noInputFile
      |exit zero on --help $help
      |print usage on no input file $usageOnNoInputFile
      |print usage on --help $usageOnHelp
      |fail on a non-existent path $nonExistentPath
      |accept relative paths $relativePaths
      |accept absolute paths $absolutePaths
      |
      |verify correct proofs
      |$correctProofs
      |fail incorrect proofs
      |$incorrectProofs
    """.stripMargin
  }
}
