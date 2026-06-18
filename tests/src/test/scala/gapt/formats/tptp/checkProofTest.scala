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
import gapt.formats.tptp.TptpProofImportError

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
        checkProof(InputFile.fromString("")) must beAnInstanceOf[SzsStatus.NotVerified]
      }

      "throw an exception on an input file without a conjecture" in {
        val input = InputFile.fromString("fof(a1, axiom, p(a) & ~p(b), file('example1_c.p',a1)).")
        checkProof(input) must beAnInstanceOf[SzsStatus.NotVerified]
      }

      "throw an exception on an input file without a $false inference" in {
        val input = InputFile.fromString("""
        |fof(a, axiom, p(a)).
        |fof(c, conjecture, p(a)).
        |fof(nc, negated_conjecture, ~p(a), inference(negated_conjecture, [status(cth)], [c])).""".stripMargin)
        checkProof(input) must beAnInstanceOf[SzsStatus.NotVerified]
      }

      "should fail on negated conjecture if conclusion is not implied by negation of conjecture" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p(a)).
        |fof(a2, axiom, ~p(a)).
        |fof(c, conjecture, p(a)).
        |fof(nc, negated_conjecture, p(a), inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc, a2])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.IncorrectNegatedConjectureInference)
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

      "should fail on negated conjecture step with thm status" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(thm)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.NegatedConjectureWithInvalidStatus)
      }

      "should fail on negated conjecture without a status" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.NegatedConjectureWithInvalidStatus)
      }

      "should fail on negated conjecture inference with more than one distinct statuses" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth),status(thm)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.NegatedConjectureWithInvalidStatus)
      }

      "should verify negated conjecture inference with more than one equal cth statuses" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth),status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.Verified
      }

      "should fail on negated conjecture step whose parent is not a conjecture" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [a1])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.NegatedConjectureWithNonConjectureParent)
      }

      "should fail on negated conjecture step without a parent" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.NegatedConjectureWithoutParent)
      }
      "should do X on negated conjecture step which has conjecture and non-conjecture parents" in todo
      "should do X on negated conjecture step with multiple conjecture parents" in todo

      "should do X on plain inference without parents" in todo
      "should fail on plain inference without status" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.PlainInferenceWithInvalidStatus)
      }

      "should fail on plain inference with more than one distinct statuses" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm),status(esa)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.PlainInferenceWithInvalidStatus)
      }

      "should fail on plain inference with cth status" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(cth)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.PlainInferenceWithInvalidStatus)
      }

      "should verify on plain inference with esa status" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(esa)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.Verified
      }

      "should fail on plain inference with cth status" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(cth)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.PlainInferenceWithInvalidStatus)
      }

      "should fail on plain inference whose parent is a conjecture" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(inf_p, plain, p, inference(p, [status(thm)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [inf_p, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.PlainInferenceWithConjectureParent)
      }

      "should verify plain inference with nested inference sources" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(inf_p, plain, p, inference(cnf, [status(thm)], [inference(normalize, [status(thm)], [a1])])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [inf_p, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.Verified
      }

      "should fail on input where formula doesn't match formula from import" in todo
      "should fail on file source, if claimed formula doesn't match formula from file" in todo
      "should do X on a file source, if the file doesn't exist" in todo("specify")

      "should fail if an axiom is used that doesn't occur in the input problem" in todo
      "should do X on an axiom with a source that only refers to another axiom" in todo("specify")

      // we are not handling such cases right now and assume that in that case
      // skolemization would be applied first so
      "should not verify on input that contains inferences with strong quantifiers without skolemization" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, ?[X]: p(X)).
        |fof(c, conjecture, ?[X]: p(X)).
        |fof(nc, negated_conjecture, ~(?[X]: p(X)), inference(negated_conjecture, [status(cth)], [c])).
        |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        checkProof(input) must beAnInstanceOf[SzsStatus.NotVerified]
      }

      "should fail on skolemization step without esa status" in todo
      "should fail on skolemization step without new_symbols" in todo
      "should throw exception on skolemization step with more than one new symbol" in todo
      "should fail on skolemization step that doesn't specify variable to be skolemized" in todo
      "should fail on proof with incorrect skolemization step" in todo("figure out possible failure scenarios skolemization")

      "should fail on axiom step without thm status" in todo
      "should fail on axiom step without file directive" in todo
      "should fail on axiom step with file directive, but without label to a formula" in todo
      "should fail on axiom step with file directive that points to non-existent file" in todo
      "should fail on axiom step with file directive that points to non-parsable problem file" in todo
      "should fail on axiom step with file directive that points to file that doesn't contain the label" in todo
      "should fail on axiom step with file directive that points to formula which is not alpha-equivalent to formula in step" in todo
      "should verifiy an axiom step with correct file directive, existent label in problem file and step formula and referred to formula are alpha-equivalent" in todo
      "should verify axiom step verify if label in problem file differs from label in proof file" in todo

      "should fail on proof with two steps with the same name if proof steps are different" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(a1, axiom, q).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.DifferentFormulasWithSameName)
      }

      "should verify proof with two steps with the same name if proof steps are equal" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.Verified
      }

      "should fail on proof with inference steps that form a 1-step cycle" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [cont])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.InferenceCycle)
      }

      "should fail on proof with inference steps that form a 2-step cycle" in {
        val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont1, plain, p, inference(fromFalsum, [status(thm)], [cont2])).
        |fof(cont2, plain, $false, inference(falsum, [status(thm)], [cont1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.failed(TptpProofImportError.InferenceCycle)
      }
      "should fail on proof with named parents that don't exist in proof" in todo
      "should throw exception on proof with invalid tptp syntax" in todo

      "should not verify proof that contains inference parents which are not simple names" in todo
      "should not verify if input has include directives (we do not support this yet)" in {
        val input = InputFile.fromString("""
        |include('filename', [a]).
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
        checkProof(input) must_== SzsStatus.cannotHandleInput
      }

      "should do X on negated conjecture if negation of conjecture is not implied by conclusion" in todo("specify")
      "should do X on a proof that doesn't use negated conjecture" in todo("specify")
      "should do X if input has no negated conjecture" in todo("specify")

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
    def foreachPath(paths: Seq[Path])(f: Path => Fragment): Fragments = {
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
      val correctProofs = foreachPath(os.walk(testResourcesRoot / "proover_competition" / "Proofs").filter(_.baseName.startsWith("correct_"))) { example =>
        val relativePath = example.relativeTo(testResourcesRoot)
        s"verify $relativePath correctly" ! (check(example) must_== SzsStatus.Verified)
      }

      val incorrectProofs = foreachPath(os.walk(testResourcesRoot / "proover_competition" / "Proofs").filter(_.baseName.startsWith("incorrect_"))) { example =>
        val relativePath = example.relativeTo(testResourcesRoot)
        s"fail verification of $relativePath" ! (check(example) must beAnInstanceOf[SzsStatus.FailedVerified])
      }

      correctProofs ^ incorrectProofs
    }

    val timeout = 25.seconds
    s2"""
    |checkProof1
    |${spec(i => checkProof1(i, timeout))}
  """.stripMargin
  }
}
