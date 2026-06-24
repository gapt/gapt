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
import gapt.formats.tptp.IncorrectInference
import gapt.formats.tptp.NegatedConjectureStepWithNonConjectureParent
import gapt.formats.tptp.NegatedConjectureWithoutParent
import gapt.formats.tptp.PlainInferenceWithConjectureParent
import gapt.formats.tptp.DifferentFormulasWithSameName
import gapt.formats.tptp.InferenceCycle
import gapt.formats.tptp.StepWithInvalidStatus
import gapt.formats.tptp.SkolemizationStepWithoutNewSymbols
import gapt.formats.tptp.SkolemizationStepWithoutBinding
import org.specs2.execute.PendingException
import gapt.formats.tptp.NegatedConjectureWithMultipleDistinctParents
import gapt.formats.tptp.StepWithMissingParents
import gapt.formats.tptp.DeskolemizationFailed

val testResourcesRoot = os.Path(this.getClass.getResource("/").toURI)
val fileDirectiveRoot = testResourcesRoot / "proover_competition" / "Proofs"

class checkProofUnitTest extends mutable.Specification {
  def todo(message: String): Pending = {
    throw new PendingException(Pending(s"TODO: $message"))
  }
  def spec(check: sourcecode.Text[InputFile => SzsStatus]) = {
    val checkProof = check.value
    s"${check.source}" should {
      "return Verified on trivial proof" in {
        val input = InputFile.fromString("""
        |fof(c, conjecture, $true).
        |fof(nc, negated_conjecture, $false, inference(nc, [status(cth)], [c])).""".stripMargin)
        checkProof(input) must_== SzsStatus.VerifiedGood
      }

      "negated conjecture" in {
        "fail on negated conjecture if conclusion is not implied by negation of conjecture" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p(a), file('Problems/test1.p', a1)).
            |fof(a2, axiom, ~p(a), file('Problems/test1.p', a2)).
            |fof(c, conjecture, p(a)).
            |fof(nc, negated_conjecture, p(a), inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc, a2])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[IncorrectInference]
          }
        }

        "verify a proof that contains unused incorrect conjecture to negated_conjecture inference but is otherwise correct" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p(a), file('Problems/test1.p', a1)).
            |fof(a2, axiom, ~p(a), file('Problems/test1.p', a2)).
            |fof(c, conjecture, p(a)).
            |fof(nc, negated_conjecture, p(a), inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, a2])).""".stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }

        "fail on negated conjecture step with thm status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(thm)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on negated conjecture without a status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on negated conjecture inference with more than one distinct statuses" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth),status(thm)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "verify negated conjecture inference with more than one equal cth statuses" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth),status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }

        "fail on negated conjecture step whose parent is not a conjecture" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [a1])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[NegatedConjectureStepWithNonConjectureParent]
          }
        }

        "fail on negated conjecture step without a parent" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[NegatedConjectureWithoutParent]
          }
        }

        "fail on negated conjecture step which has multiple distinct parents" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c, a1])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[NegatedConjectureWithMultipleDistinctParents]
          }
        }

        "succeed on negated conjecture step with multiple equal conjecture parents" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c, c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }
      }

      "plain inferences" in {
        "fail on plain inference without parents if formula is not valid" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(i: IncorrectInference) => i.stepName must_== "cont"
          }
        }

        "succeed on plain inference without parents if formula is valid" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', a)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(i, plain, q | ~q, inference(tautology, [status(thm)], [])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc, i])).""".stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }

        "fail on plain inference without status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on plain inference with more than one distinct statuses" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm),status(esa)], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on plain inference with cth status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(cth)], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "verify on plain inference with esa status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(esa)], [a1, nc])).""".stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }

        "fail on plain inference with cth status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(cth)], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on plain inference whose parent is a conjecture" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(inf_p, plain, p, inference(p, [status(thm)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [inf_p, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[PlainInferenceWithConjectureParent]
          }
        }

        "verify plain inference with nested inference sources" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(inf_p, plain, p, inference(cnf, [status(thm)], [inference(normalize, [status(thm)], [a1])])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [inf_p, nc])).""".stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }

        "verify input that contains inferences with strong quantifiers if inference is easy" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, ?[X]: p(X), file('Problems/test3.p', a)).
            |fof(c, conjecture, ?[X]: p(X), file('Problems/test3.p', c)).
            |fof(nc, negated_conjecture, ~(?[X]: p(X)), inference(negated_conjecture, [status(cth)], [c])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must_=== SzsStatus.VerifiedGood
        }
      }

      "skolemization" in {
        "fail on skolemization step without esa status" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X)).
            |fof(c, conjecture, ![X]: p(X)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(sK0), inference(skolemize, [new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on skolemization step without new_symbols" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X)).
            |fof(c, conjecture, ![X]: p(X)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(sK0), inference(skolemize, [status(esa), skolemize(X, sK0)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: SkolemizationStepWithoutNewSymbols) => reason.stepName must_== "nc_skolem"
          }
        }

        "not verify skolemization step with more than one new symbol" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X, Y]: p(X, Y)).
            |fof(c, conjecture, ![X]: p(X, a)).
            |fof(nc, negated_conjecture, ?[X, Y]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(sK0, sK1), inference(skolemize, [status(esa), new_symbols(skolem, [sK0, sK1]), skolemize(X, sK0), skolemize(Y, sK1)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.Unknown(_: NotVerifiedReason.CannotHandleInput) => ok
          }
        }

        "fail on skolemization step that doesn't specify variable to be skolemized" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X), file('Problems/test4.p', a)).
            |fof(c, conjecture, ![X]: p(X), file('Problems/test4.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0])], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: SkolemizationStepWithoutBinding) => reason.stepName must_== "nc_skolem"
          }
        }

        "fail on proof where claimed formula is not the skolemization of the parent given the binding" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X), file('Problems/test4.p', a)).
            |fof(c, conjecture, ![X]: p(X), file('Problems/test4.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(sK1), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: IncorrectInference) => reason.stepName must_== "nc_skolem"
          }
        }

        "fail on proof where skolemization step introduces a symbol that is already present in parent formula" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X, a), file('Problems/test9.p', a)).
            |fof(c, conjecture, ![X]: p(X, a), file('Problems/test9.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X, a), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(a, a), inference(skolemize, [status(esa), new_symbols(skolem, [a]), skolemize(X, a)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: IncorrectInference) => reason.stepName must_== "nc_skolem"
          }
        }

        "allow outer skolemization deeply nested inside the formula" in todo

        "fail on proof where skolemization step introduces a symbol already used in non-parent resulting in incorrect derivation" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p(a), file('Problems/test10.p', a)).
            |fof(c, conjecture, ![X]: p(X), file('Problems/test10.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(a), inference(skolemize, [status(esa), new_symbols(skolem, [a]), skolemize(X, a)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(r) => r must beAnInstanceOf[DeskolemizationFailed]
          }
        }

        "verify proof with skolemization where axiom is instantiated by skolem term" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X), file('Problems/test4.p', a)).
            |fof(c, conjecture, ![X]: p(X), file('Problems/test4.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(i, plain, p(a), inference(instance, [status(thm)], [a])).
            |fof(nc_skolem, plain, ~p(a), inference(skolemize, [status(esa), new_symbols(skolem, [a]), skolemize(X, a)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [i, nc_skolem])).""".stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }
      }

      "axiom file directive" in {
        "fail on axiom step without thm status" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p).
            |fof(c, conjecture, $true).
            |fof(nc, negated_conjecture, $false, inference(negated_conjecture, [status(cth)], [c])).
            """.stripMargin)
          todo("not clear how to enforce this since axiom should also have file directive which doesn't allow setting status")
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: StepWithInvalidStatus) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step without file directive" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: OtherFailureReason.AxiomSourceMissing) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with a non-file source" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, unknown).
            |fof(c, conjecture, p, unknown).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: OtherFailureReason.AxiomFileDirectiveMissing) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive, but without label to a formula" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p')).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: OtherFailureReason.AxiomFileDirectiveLabelMissing) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to non-existent file" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/nonexistent.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: OtherFailureReason.AxiomFileDirectiveFileNotFound) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to non-parsable problem file" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/invalid-tptp-syntax.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: OtherFailureReason.AxiomFileDirectiveInvalidSyntax) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to file that doesn't contain the label" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p', a0)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: OtherFailureReason.AxiomFileDirectiveFileDoesNotHaveLabel) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to formula which is not alpha-equivalent to formula in step" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test5.p', a)).
            |fof(c, conjecture, p, file('Problems/test5.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: OtherFailureReason.AxiomFileDirectiveFormulaNotAlphaEquivalentToClaimedFormula) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to a label which is not unique and some of the labels have different formulas" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test6.p', a)).
            |fof(c, conjecture, p, file('Problems/test6.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: OtherFailureReason.AxiomFileDirectiveFormulaHasMultipleDistinctFormulasWithLabel) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to formula which is not an axiom" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test7.p', a)).
            |fof(c, conjecture, p, file('Problems/test7.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason: OtherFailureReason.AxiomFileDirectiveStepIsNotAnAxiom) => reason.stepName must_== "a"
          }
        }

        "verify an axiom step with correct file directive, existent label in problem file and step formula and referred to formula are alpha-equivalent" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }

        "verify axiom step even if label in problem file differs from label in proof file" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c1, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c1])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).
            """.stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }

        "verify axiom step even if there are steps with same label, if they are equal in role and have alpha-equivalent formulas" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test8.p', a)).
            |fof(c1, conjecture, p, file('Problems/test8.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c1])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).
            """.stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }

        "verify axiom step if given correct absolute path" in {
          val input = InputFile.fromString(s"""
            |fof(a1, axiom, p, file('${fileDirectiveRoot}/Problems/test8.p', a)).
            |fof(c1, conjecture, p, file('Problems/test8.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c1])).
            |fof(cont, plain, $$false, inference(falsum, [status(thm)], [a1, nc])).
            """.stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }

        "verify if an unused axiom step has missing file directive if derivation is otherwise correct" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(unused, axiom, q).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }
      }

      "distinct names" in {
        "fail on proof with two steps with the same name if proof steps are different" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(a1, axiom, q).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[DifferentFormulasWithSameName]
          }
        }

        "verify proof with two steps with the same name if proof steps are equal" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must_== SzsStatus.VerifiedGood
        }
      }

      "inference parents" in {
        "fail on proof with inference steps that form a 1-step cycle" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [cont])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[InferenceCycle]
          }
        }

        "fail on proof with inference steps that form a 2-step cycle" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont1, plain, p, inference(fromFalsum, [status(thm)], [cont2])).
            |fof(cont2, plain, $false, inference(falsum, [status(thm)], [cont1, nc])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[InferenceCycle]
          }
        }

        "fail on proof with inference parents that does not exist in proof" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont2, plain, $false, inference(falsum, [status(thm)], [nc, a])).""".stripMargin)
          checkProof(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithMissingParents]
          }
        }
      }

      "unknown status" in {
        "not verify an empty input file" in {
          checkProof(InputFile.fromString("")) must beAnInstanceOf[SzsStatus.Unknown]
        }

        "not verify an input file without a conjecture" in {
          val input = InputFile.fromString("fof(a1, axiom, p(a) & ~p(b), file('example1_c.p',a1)).")
          checkProof(input) must beAnInstanceOf[SzsStatus.Unknown]
        }

        "not verify an input file without a $false inference" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p(a)).
            |fof(c, conjecture, p(a)).
            |fof(nc, negated_conjecture, ~p(a), inference(negated_conjecture, [status(cth)], [c])).""".stripMargin)
          checkProof(input) must beAnInstanceOf[SzsStatus.Unknown]
        }

        "not verify proof with invalid tptp syntax" in {
          // in the following, the dots at the end of lines are missing to get an
          // invalid tptp syntax file
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a))
            |fof(c, conjecture, p, file('Problems/test2.p', c))
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c]))
            |fof(cont2, plain, $false, inference(falsum, [status(thm)], [nc, a]))""".stripMargin)
          checkProof(input) must beAnInstanceOf[SzsStatus.Unknown]
        }

        "not verify if input has include directives (we do not support this yet)" in {
          todo
          val input = InputFile.fromString("""
            |include('filename', [a]).
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkProof(input) must_== SzsStatus.cannotHandleInput
        }
      }

      "do fail if a skolem symbol has a symbol occurring in the conjecture" in todo
      "do X on axiom and conjecture steps that import different files" in todo("specify")
      "do X on an axiom with a source that only refers to another axiom" in todo("specify")
      "do X on negated conjecture step with inference record parent" in todo("specify")
      "do X on negated conjecture if negation of conjecture is not implied by conclusion" in todo("specify")
      "do X if input has no conjecture" in todo("specify")
      "do X if input has more than one conjecture" in todo("specify")
      "do X if input has no negated conjecture" in todo("specify")
      "do X on conjecture with incorrect file directive" in todo("specify")
      "do X if input has more than one negated conjecture" in todo("specify")
      "do X if input has no $false proof step" in todo("specify")
      "do X if input has more than one $false proof step" in todo("specify")
      "do X on inputs with higher-order formulas" in todo("specify")

      "fail on plain inference with esa status if not equi-satisfiable" in todo
    }
  }

  val timeout = 1.second
  spec(i => checkProof(i, fileDirectiveRoot, timeout = timeout))
}

class checkProofExampleTest extends Specification {

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
        s"verify $relativePath correctly" ! (check(example) must_== SzsStatus.VerifiedGood)
      }

      val incorrectProofs = foreachPath(os.walk(testResourcesRoot / "proover_competition" / "Proofs").filter(_.baseName.startsWith("incorrect_"))) { example =>
        val relativePath = example.relativeTo(testResourcesRoot)
        s"fail verification of $relativePath" ! (check(example) must beAnInstanceOf[SzsStatus.VerifiedBad])
      }

      correctProofs ^ incorrectProofs
    }

    val timeout = 25.seconds
    s2"""
    |checkProof1
    |${spec(i => checkProof(i, fileDirectiveRoot, timeout = timeout))}
  """.stripMargin
  }
}
