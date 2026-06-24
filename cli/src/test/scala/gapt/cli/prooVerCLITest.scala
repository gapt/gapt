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

class prooVerCLITest extends Specification with BeforeAll {
  private val usageText =
    """
      |./gapt-check <PROOF>
      |
      |Checks the correctness of a given proof.
      |PROOF is a path to a TSTP proof file""".stripMargin.strip

  trait Cwd { def path: Path }
  object RepoRoot extends Cwd { def path: Path = os.pwd / os.up }
  object TestResources extends Cwd {
    def path: Path = RepoRoot.path / "tests" / "src" / "test" / "resources" / "proover_competition"
  }

  val prooVerCLIZip = RepoRoot.path / "target" / "gapt-ProoVer.zip"
  val prooVerCLIZipUnpackDirectory = RepoRoot.path / "target" / "gapt-ProoVer"
  val prooVerCLIScript = RepoRoot.path / "target" / "gapt-ProoVer" / "gapt-check"
  val testDerivations = TestResources.path / "Proofs"

  private def prepareGaptCheckScript(): Unit = {
    assert(os.exists(prooVerCLIZip))
    os.remove.all(prooVerCLIZipUnpackDirectory)
    val exitCode = Process(Seq("unzip", prooVerCLIZip.toString, "-d", prooVerCLIZipUnpackDirectory.toString)).!
    assert(exitCode == 0)
    assert(os.exists(prooVerCLIScript))
  }

  private def proofCheckerProcess(args: String*)(using cwd: Cwd): ProcessBuilder =
    Process(Seq("sh", prooVerCLIScript.toString) ++ args, cwd.path.toIO)

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

  override def beforeAll(): Unit = prepareGaptCheckScript()

  def is: SpecStructure = {
    given cwd: Cwd = TestResources

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
        proofCheckerProcess("./Proofs/non_existing_file.p").!!!

      (exitCode must beGreaterThan(0)).and(stdout must beEmpty).and(stderr must startWith("file not found"))
    }

    def relativePaths: Result = {
      val (exitCode, _, _) =
        proofCheckerProcess("./Proofs/correct_example1_c_proof.p").!!!

      exitCode must_== 0
    }

    def absolutePaths: Result = {
      val (exitCode, _, _) =
        proofCheckerProcess(s"${cwd.path}/Proofs/correct_example1_c_proof.p").!!!

      exitCode must_== 0
    }

    def verifyCorrect(example: Path): Result = {
      val (exitCode, stdout, _) =
        proofCheckerProcess(example.toString).!!!

      (exitCode must_== 0).and(
        stdout must_== "%SZS status VerifiedGood"
      )
    }

    def failVerification(example: Path): Result = {
      val (exitCode, stdout, _) =
        proofCheckerProcess(example.toString).!!!

      (exitCode must_== 0)
        .and(stdout must startWith("%SZS status VerifiedBad"))
        .and(stdout.linesIterator.take(2).size must_== 1)
    }

    def foreachPath(paths: Seq[Path])(f: Path => Fragment): Fragments = {
      Fragments.foreach(paths) { path =>
        val fragment = f(path)
        val relativePath = path.relativeTo(testDerivations)
        val pathFragment =
          if path.last.startsWith("skip") then
            fragment.setExecution(Execution.result(skipped(s"not testing $relativePath as it is marked skipped")))
          else fragment
        br ^ t ^ pathFragment ^ bt ^ br
      }
    }

    val correctProofs =
      val correctProofPaths = os.walk(testDerivations)
        .filter(_.baseName.startsWith("correct_"))
      foreachPath(correctProofPaths) { example =>
        val relativePath = example.relativeTo(TestResources.path)
        s"verify $relativePath correctly" ! verifyCorrect(example)
      }

    val incorrectProofs =
      val incorrectProofPaths = os.walk(testDerivations)
        .filter(_.baseName.startsWith("incorrect_"))
      foreachPath(incorrectProofPaths) { example =>
        val relativePath = example.relativeTo(TestResources.path)
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
