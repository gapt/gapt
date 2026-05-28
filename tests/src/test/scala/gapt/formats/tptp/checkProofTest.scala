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
import org.specs2.execute.Pending
import scala.concurrent.duration._

class checkProofUnitTest extends mutable.Specification {
  def todo(message: String): Pending = Pending(s"TODO: $message")
  def spec(check: sourcecode.Text[InputFile => SzsStatus]) = {
    val checkProof = check.value
    s"${check.source}" should {
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
        val input = InputFile.fromString("fof(a1, axiom, p(a) & ~p(b), file('example1_c.p',a1)).")
        checkProof(input) must throwAn[Exception]
      }

      "throw an exception on an input file without a $false inference" in {
        val input = InputFile.fromString("""
        |fof(a, axiom, p(a)).
        |fof(c, conjecture, p(a)).
        |fof(nc, negated_conjecture, ~p(a), inference(negated_conjecture, [status(cth)], [c])).""".stripMargin)
        checkProof(input) must throwAn[Exception]
      }

      "should fail on negated conjecture if conclusion is not implied by negation of conjecture" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p(a)).
        |fof(a2, axiom, ~p(a)).
        |fof(c, conjecture, p(a)).
        |fof(nc, negated_conjecture, p(a), inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc, a2])).""".stripMargin)
        checkProof(input) must_== SzsStatus.FailedVerified
      }

      "should verify a proof that contains unused incorrect conjecture to negated_conjecture inference but is otherwise correct" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p(a)).
        |fof(a2, axiom, ~p(a)).
        |fof(c, conjecture, p(a)).
        |fof(nc, negated_conjecture, p(a), inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, a2])).""".stripMargin)
        checkProof(input) must_== SzsStatus.Verified
      }

      "should fail on negated conjecture step without cth status" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        todo
        checkProof(input) must_== SzsStatus.FailedVerified
      }

      "should fail on negated conjecture without a status" in todo
      "should fail on plain inference with more than one distinct statuses" in todo
      "should fail on negated conjecture step whose parent is not a conjecture" in todo
      "should fail on negated conjecture step without a parent" in todo

      "should fail on input where formula doesn't match formula from import" in todo

      "should fail on plain inference without parents" in todo
      "should fail on plain inference without status" in todo
      "should fail on plain inference with more than one distinct statuses" in todo

      "should fail on skolemization step without esa status" in todo
      "should fail on skolemization step without new_symbols" in todo
      "should throw exception on skolemization step with more than one new symbol" in todo
      "should fail on skolemization step that doesn't specify variable to be skolemized" in todo
      "should fail on proof with incorrect skolemization step" in todo("figure out possible failure scenarios skolemization")

      "should fail on proof with two steps with the same name if proof steps are different" in todo
      "should fail on proof with two steps with the same name even if proof steps are equal" in todo
      "should fail on proof with inference steps that form a cycle" in todo
      "should throw exception on proof with invalid tptp syntax" in todo

      "should fail on negated conjecture if negation of conjecture is not implied by conclusion" in todo("specify")
      "should do X on a proof that doesn't use negated conjecture" in todo("specify")
      "should do X if input has not negated conjecture" in todo("specify")

      "should do X if an inference has two distinct statuses" in todo("specify")
      "should do X if input has no conjecture" in todo("specify")
      "should do X if input has no $false proof step" in todo("specify")
      "should do X if input has more than one conjecture" in todo("specify")
      "should do X if input has more than one $false proof step" in todo("specify")
    }
  }

  val timeout = 1.second
  spec(i => checkProof1(i, timeout))
  // spec(checkProof2)
}

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

    val timeout = 25.seconds
    s2"""
    |checkProof1
    |${spec(i => checkProof1(i, timeout))}
    |checkProof2
    |${spec(i => checkProof2(i))}
  """.stripMargin
  }
}
