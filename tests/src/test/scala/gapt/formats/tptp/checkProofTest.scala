package gapt.formats.tptp.check

import gapt.formats.InputFile
import org.specs2.Specification
import org.specs2.mutable
import org.specs2.specification.core.SpecStructure
import os.Path
import org.specs2.execute.Result
import org.specs2.specification.core.Fragments
import org.specs2.specification.core.Fragment
import org.specs2.specification.core.Execution

class checkProofExampleTest extends Specification {
  val testResourcesRoot = os.Path(getClass.getResource("/").toURI)

  def is: SpecStructure = {
    def foreachPath(directory: Path)(f: Path => Fragment): Fragments = {
      val paths = os.list(directory)
      Fragments.foreach(paths) { path =>
        val fragment = f(path)
        val relativePath = path.relativeTo(testResourcesRoot)
        val pathFragment =
          if path.last.startsWith("skip") then
            fragment.setExecution(Execution.result(skipped(s"not testing $relativePath as it is marked skipped")))
          else fragment
        br ^ t ^ pathFragment ^ bt ^ br
      }
    }

    def spec(check: InputFile => SzsStatus): Fragments = {
      val correctProofs = foreachPath(testResourcesRoot / "proover_competition" / "proofs" / "correct") { example =>
        val relativePath = example.relativeTo(testResourcesRoot)
        s"verify $relativePath correctly" ! (check(example) must_== SzsStatus.Verified)
      }

      val incorrectProofs = foreachPath(testResourcesRoot / "proover_competition" / "proofs" / "incorrect") { example =>
        val relativePath = example.relativeTo(testResourcesRoot)
        s"fail verification of $relativePath" ! (check(example) must_== SzsStatus.FailedVerified)
      }

      correctProofs ^ incorrectProofs
    }

    s2"""
    |checkProof1
    |${spec(checkProof1)}
    |checkProof2
    |${spec(checkProof2)}
  """.stripMargin
  }
}

class checkProofUnitTest extends mutable.Specification {
  def spec(check: sourcecode.Text[InputFile => SzsStatus]) = {
    s"${check.source}" should {
      val checkProof = check.value
      "should return Verified on trivial proof" in {
        val input = InputFile.fromString("""
        |fof(c, conjecture, $true).
        |fof(nc, negated_conjecture, $false, inference(nc, [status(cth)], [c])).""".stripMargin)
        checkProof(input) must_== SzsStatus.Verified
      }

      "throw an exception on empty input file" in {
        checkProof(InputFile.fromString("")) must throwAn[Exception]
      }

      "throw an exception on an input file without a conjecture" in {
        checkProof(InputFile.fromString("fof(a1, axiom, p(a) & ~p(b), file('example1_c.p',a1)).")) must throwAn[Exception]
      }
    }
  }

  spec(checkProof1)
  spec(checkProof2)
}
