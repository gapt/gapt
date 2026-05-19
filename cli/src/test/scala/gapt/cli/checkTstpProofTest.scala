package gapt.cli

import org.specs2.mutable.Specification
import org.specs2.specification.BeforeAll
import org.specs2.specification.core.Fragments

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
  object TestCwd extends Cwd { def path: Path = os.pwd }
  object RepoRoot extends Cwd { def path: Path = os.pwd / os.up }
  object ProoverCompetitionRoot extends Cwd {
    def path: Path = RepoRoot.path / "examples" / "proover_competition"
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

  "checkProof" should {
    given cwd: Cwd = RepoRoot

    "exit non-zero on no input file" in {
      val (exitCode, _, _) = proofCheckerProcess().!!!
      exitCode must beGreaterThan(0)
    }

    "exit zero on --help" in {
      val (exitCode, _, _) = proofCheckerProcess("--help").!!!
      exitCode must_== 0
    }

    "print usage on no input file" in {
      val (_, _, stderr) = proofCheckerProcess().!!!
      stderr must startWith(usageText)
    }

    "print usage on --help" in {
      val (_, stdout, _) = proofCheckerProcess("--help").!!!
      stdout must startWith(usageText)
    }

    "fail on a non-existent path" in {
      val (exitCode, stdout, stderr) =
        proofCheckerProcess("./examples/proover_competition/proofs/non_existing_file.p").!!!

      exitCode must beGreaterThan(0)
      stdout must beEmpty
      stderr must startWith("file not found")
    }

    "accept relative paths" in {
      val (exitCode, _, _) =
        proofCheckerProcess("./examples/proover_competition/proofs/correct/example1_c_proof.p").!!!

      exitCode must_== 0
    }

    "accept absolute paths" in {
      val (exitCode, _, _) =
        proofCheckerProcess(s"${cwd.path}/examples/proover_competition/proofs/correct/example1_c_proof.p").!!!

      exitCode must_== 0
    }

    def selectProofsFromDirectory(dir: Path) =
      os.list(dir).filterNot(_.last.startsWith("skip"))

    val correctProofExamples = selectProofsFromDirectory(cwd.path / "examples" / "proover_competition" / "proofs" / "correct")
    Fragments.foreach(correctProofExamples) { example =>
      given Cwd = ProoverCompetitionRoot
      s"verify $example correctly" in {
        val (exitCode, stdout, _) =
          proofCheckerProcess(example.toString).!!!

        exitCode must_== 0
        stdout must_== "%SZS status Verified"
      }
    }

    val incorrectProofExamples = selectProofsFromDirectory(cwd.path / "examples" / "proover_competition" / "proofs" / "incorrect")
    Fragments.foreach(incorrectProofExamples) { example =>
      given Cwd = ProoverCompetitionRoot
      s"fail verification of $example" in {
        val (exitCode, stdout, _) =
          proofCheckerProcess(example.toString).!!!

        exitCode must_== 0
        stdout must_== "%SZS status FailedVerified"
      }
    }
  }
}
