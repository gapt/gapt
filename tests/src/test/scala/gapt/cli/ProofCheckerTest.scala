package gapt.cli

import org.specs2.mutable.Specification
import org.specs2.specification.BeforeAll
import org.specs2.specification.core.Fragments

import os.Path
import scala.sys.process._

class ProofCheckerTest extends Specification with BeforeAll {
  private val usageText =
    """check-proof PROOF
      |
      |Checks the correctness of a given proof.
      |PROOF is a path to a TSTP proof file""".stripMargin

  trait Cwd { def path: Path }
  object TestCwd extends Cwd { def path: Path = os.pwd }
  object RepoRoot extends Cwd { def path: Path = os.pwd / os.up }
  object ProoverCompetitionRoot extends Cwd {
    def path: Path = RepoRoot.path / "examples" / "proover_competition"
  }

  private def assemble(): Unit = {
    println("assembling proof checker")
    val exitCode = Process(
      Seq(
        "sbt",
        "--error",
        "--batch",
        """set cli / assembly / mainClass := Some("gapt.cli.checkProof")""",
        """set cli / assembly / assemblyOutputPath := target.value / "proof-checker.jar"""",
        "cli / assembly"
      ),
      RepoRoot.path.toIO
    ).!
    assert(os.exists(RepoRoot.path / "target" / "proof-checker.jar"))
    assert(exitCode == 0, "expected a zero exit code, but got non-zero")
  }

  private def proofCheckerProcess(args: String*)(using cwd: Cwd): ProcessBuilder =
    Process(
      Seq("java", "-jar", (RepoRoot.path / "target" / "proof-checker.jar").toString) ++ args,
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

  override def beforeAll(): Unit = assemble()

  "checkProof" should {
    given cwd: Cwd = RepoRoot

    "exit zero on no input file" in {
      val exitCode = proofCheckerProcess().!
      exitCode must_== 0
    }

    "print usage on no input file" in {
      val output = proofCheckerProcess().!!
      output must startWith(usageText)
    }

    "fail on a non-existent path" in {
      val (exitCode, stdout, stderr) =
        proofCheckerProcess("./examples/proover_competition/proofs/non_existing_file.p").!!!

      exitCode must not(be_==(0))
      stdout must beEmpty
      stderr must startWith("file not found")
    }

    "accept relative paths" in {
      val exitCode =
        proofCheckerProcess("./examples/proover_competition/proofs/example1_c_proof.p").!

      exitCode must_== 0
    }

    "accept absolute paths" in {
      val exitCode =
        proofCheckerProcess(s"${cwd.path}/examples/proover_competition/proofs/example1_c_proof.p").!

      exitCode must_== 0
    }

    val correctProofExamples = Seq(
      "example1_c_proof.p",
      "example2_c_proof.p",
      "example3_c_proof.p"
    )
    Fragments.foreach(correctProofExamples) { example =>
      given Cwd = ProoverCompetitionRoot
      s"verify $example correctly" in {
        val (exitCode, stdout, stderr) =
          proofCheckerProcess(s"./proofs/$example").!!!

        exitCode must_== 0
        stdout.linesIterator.toSeq.last must startWith("%SZS status Verified")
        stderr must beEmpty
      }
    }

    val incorrectProofExamples = Seq(
      "example1_e_proof.p",
      "example2_e_proof.p",
      "example3_e_proof.p",
      "example4_e_proof.p"
    )
    Fragments.foreach(incorrectProofExamples) { example =>
      given Cwd = ProoverCompetitionRoot
      s"fail verification of $example" in {
        val (exitCode, stdout, stderr) =
          proofCheckerProcess(s"./proofs/$example").!!!

        exitCode must_== 0
        stdout.linesIterator.toSeq.last must startWith("%SZS status FailedVerified")
        stderr must beEmpty
      }
    }
  }
}
