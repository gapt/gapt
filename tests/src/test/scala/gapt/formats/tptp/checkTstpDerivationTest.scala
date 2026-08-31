package gapt.formats.tptp.check

import gapt.expr.formula.fol.FOLConst
import gapt.formats.InputFile
import gapt.formats.StringInputFile
import gapt.proofs.SequentMatchers

import org.specs2.Specification
import org.specs2.execute.Pending
import org.specs2.execute.PendingException
import org.specs2.execute.Result
import org.specs2.mutable
import org.specs2.specification.core.Execution
import org.specs2.specification.core.Fragment
import org.specs2.specification.core.Fragments
import org.specs2.specification.core.SpecStructure
import os.Path

import scala.concurrent.duration.*
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.stringInterpolationForExpressions
import gapt.logic.Polarity.Positive
import gapt.expr.formula.hol.HOLPosition
import gapt.formats.ClasspathInputFile
import gapt.formats.tptp.check.FindSkolemizableInstance.QuantifierType
import gapt.logic.Polarity.Negative
import gapt.provers.escargot.Escargot
import gapt.utils.EitherHelpers.RichEither
import gapt.utils.withTimeout
import gapt.proofs.lk.rules.ProofLink
import gapt.expr.formula.Bottom

val testResourcesRoot = os.Path(this.getClass.getResource("/").toURI)
val fileDirectiveRoot = os.pwd / "src" / "test" / "resources" / "proover_competition" / "Proofs"
given resolver: FileNameResolver = FileNameResolver.absolute.relativeTo(fileDirectiveRoot)

class checkTstpDerivationUnitTest extends mutable.Specification {
  def todo(message: String): Pending = {
    throw new PendingException(Pending(s"TODO: $message"))
  }
  def spec(check: sourcecode.Text[InputFile => FileNameResolver ?=> SzsStatus]) = {
    val checkDerivation0 = check.value
    def checkDerivation(inputFile: InputFile): SzsStatus = {
      assert(inputFile.isInstanceOf[StringInputFile])
      val inputPath = fileDirectiveRoot / "input"
      val r = resolver.extend {
        case s if s == inputPath.toString => Right(inputFile.read)
        case s                            => resolver(s)
      }
      checkDerivation0(inputPath)(using r)
    }
    s"${check.source}" should {

      "return Verified on trivial proof" in {
        val input = InputFile.fromString("""
            |fof(c, conjecture, $true, file('Problems/test14.p', c)).
            |fof(nc, negated_conjecture, $false, inference(negated_conjecture, [status(cth)], [c])).""".stripMargin)
        checkDerivation(input) must_== SzsStatus.VerifiedGood
      }

      "negated conjecture" in {
        "fail on negated conjecture if conclusion is not implied by negation of conjecture" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p(a), file('Problems/test1.p', a1)).
            |fof(a2, axiom, ~p(a), file('Problems/test1.p', a2)).
            |fof(c, conjecture, p(a), file('Problems/test1.p', c)).
            |fof(nc, negated_conjecture, p(a), inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc, a2])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[IncorrectInference]
          }
        }

        "fail a proof that contains unused incorrect conjecture to negated_conjecture inference even if it is otherwise correct" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p(a), file('Problems/test1.p', a1)).
            |fof(a2, axiom, ~p(a), file('Problems/test1.p', a2)).
            |fof(c, conjecture, p(a), file('Problems/test1.p', c)).
            |fof(nc, negated_conjecture, p(a), inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, a2])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(r: IncorrectInference) => r.stepName must_== "nc"
          }
        }

        "fail on negated conjecture step with thm status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(thm)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on negated conjecture without a status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on negated conjecture inference with more than one distinct statuses" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth),status(thm)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "verify negated conjecture inference with more than one equal cth statuses" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth),status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must_== SzsStatus.VerifiedGood
        }

        "fail on negated conjecture step whose parent is not a conjecture" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [a1])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[NegatedConjectureStepWithNonConjectureParent]
          }
        }

        "fail on negated conjecture step without a parent" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[NegatedConjectureWithoutParent]
          }
        }

        "fail on negated conjecture step which has multiple distinct parents" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c, a1])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[NegatedConjectureWithMultipleDistinctParents]
          }
        }

        "succeed on negated conjecture step with multiple equal conjecture parents" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c, c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must_== SzsStatus.VerifiedGood
        }

        "fail on negated conjecture if negation of conjecture is not implied by conclusion" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              |fof(a1, axiom, p | q, file('Problems/problem.p', a1)).
              |fof(a2, axiom, ~q, file('Problems/problem.p', a2)).
              |fof(c, conjecture, p | q, file('Problems/problem.p', c)).
              |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
              |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, a2, nc])).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a1, axiom, p | q).
              |fof(a2, axiom, ~q).
              |fof(c, conjecture, p | q).
            """.stripMargin)
          }
          checkDerivation0("/input") must beLike {
            case SzsStatus.VerifiedBad(r: IncorrectInference) => r.stepName must_=== "nc"
          }
        }

        "fail on negated conjecture step without negated_conjecture inference name" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              |fof(a1, axiom, p, file('Problems/problem.p', a)).
              |fof(c, conjecture, p, file('Problems/problem.p', c)).
              |fof(nc, negated_conjecture, ~p, inference(nc, [status(cth)], [c])).
              |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, p).
              |fof(c, conjecture, p).
            """.stripMargin)
          }
          checkDerivation0("/input") must beLike {
            case SzsStatus.VerifiedBad(r: StepWithInvalidInferenceRule) => r.stepName must_=== "nc"
          }
        }

        "fail on negated conjecture step without negated_conjecture role" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              |fof(a1, axiom, p, file('Problems/problem.p', a)).
              |fof(c, conjecture, p, file('Problems/problem.p', c)).
              |fof(nc, plain, ~p, inference(negated_conjecture, [status(cth)], [c])).
              |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, p).
              |fof(c, conjecture, p).
            """.stripMargin)
          }
          checkDerivation0("/input") must beAnInstanceOf[SzsStatus.VerifiedBad]
        }

        "fail on negated conjecture step with inference record parent" in todo // parents need not be labels, only accept if chain of thm
        "handle input with multiple negated conjectures" in todo // TODO
      }

      "plain inferences" in {
        "fail on plain inference without parents if formula is not valid" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(i: IncorrectInference) => i.stepName must_== "cont"
          }
        }

        "succeed on plain inference without parents if formula is valid" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(i, plain, q | ~q, inference(tautology, [status(thm)], [])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc, i])).""".stripMargin)
          checkDerivation(input) must_== SzsStatus.VerifiedGood
        }

        "fail on plain inference without status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on plain inference with more than one distinct statuses" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm),status(esa)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on plain inference with cth status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(cth)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on plain inference with cth status" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(cth)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail on plain inference whose parent is a conjecture" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(inf_p, plain, p, inference(p, [status(thm)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [inf_p, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
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
          checkDerivation(input) must_== SzsStatus.VerifiedGood
        }

        "verify input that contains inferences with strong quantifiers if inference is easy" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, ?[X]: p(X), file('Problems/test3.p', a)).
            |fof(c, conjecture, ?[X]: p(X), file('Problems/test3.p', c)).
            |fof(nc, negated_conjecture, ~(?[X]: p(X)), inference(negated_conjecture, [status(cth)], [c])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must_=== SzsStatus.VerifiedGood
        }

        "fail on plain inference step without source" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              |fof(a1,axiom, p(a),file('Problems/PRV039+1.p',a1)).
              |fof(c,conjecture, q(a), file('Problems/PRV039+1.p',c)).
              |fof(neg,negated_conjecture, ~ q(a), inference(negated_conjecture,[status(cth)],[c])).
              |fof(s, plain, q(a)).
              |fof(bot,plain, $false, inference(consequence,[status(thm)],[neg,s])).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, p(a)).
              |fof(c, conjecture, q(a)).
            """.stripMargin)
          }
          checkDerivation0("/input") must beLike {
            case SzsStatus.VerifiedBad(s: PlainInferenceWithoutSource) => s.stepName must_== "s"
          }
        }
      }

      "skolemization" in {
        "fail on skolemization step without esa status" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X), file('Problems/test4.p', a)).
            |fof(c, conjecture, ![X]: p(X), file('Problems/test4.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(sK0), inference(skolemize, [new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[StepWithInvalidStatus]
          }
        }

        "fail verification of skolemization step without new_symbols" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X), file('Problems/test4.p', a)).
            |fof(c, conjecture, ![X]: p(X), file('Problems/test4.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(sK0), inference(skolemize, [status(esa), skolemize(X, sK0)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: SkolemizationStepWithoutNewSymbols) => reason.stepName must_== "nc_skolem"
          }
        }

        "return unknown on skolemization step with more than one new symbol" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X, Y]: p(X, Y)).
            |fof(c, conjecture, ![X]: p(X, a)).
            |fof(nc, negated_conjecture, ?[X, Y]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(sK0, sK1), inference(skolemize, [status(esa), new_symbols(skolem, [sK0, sK1]), skolemize(X, sK0), skolemize(Y, sK1)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.Unknown(_: CannotHandleInput) => ok
          }
        }

        "fail verification of skolemization step that doesn't specify variable to be skolemized" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X), file('Problems/test4.p', a)).
            |fof(c, conjecture, ![X]: p(X), file('Problems/test4.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0])], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkDerivation(input) must beLike {
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
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(IncorrectSkolemization(reason: FormulaMismatch))                        => reason.stepName must_== "nc_skolem"
            case SzsStatus.VerifiedBad(IncorrectSkolemization(reason: NoStrongQuantifierFittingSkolemization)) => reason.stepName must_== "nc_skolem"
          }
        }

        "fail on proof where skolemization step introduces a symbol that is already present in parent formula" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X, a), file('Problems/test9.p', a)).
            |fof(c, conjecture, ![X]: p(X, a), file('Problems/test9.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X, a), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(a, a), inference(skolemize, [status(esa), new_symbols(skolem, [a]), skolemize(X, a)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(IncorrectSkolemization(reason: SkolemSymbolIsAConstantExistingInTheInput)) => {
              (reason.skolemizationStepName must_== "nc_skolem")
                .and(reason.inputStepName must beAnyOf("a", "c"))
                .and(reason.const must_== FOLConst("a"))
            }
          }
        }

        "fail on proof where skolemization step introduces a symbol already used in non-parent resulting in incorrect derivation" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p(a), file('Problems/test10.p', a)).
            |fof(c, conjecture, ![X]: p(X), file('Problems/test10.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(nc_skolem, plain, ~p(a), inference(skolemize, [status(esa), new_symbols(skolem, [a]), skolemize(X, a)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [a, nc_skolem])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(IncorrectSkolemization(r: SkolemSymbolIsAConstantExistingInTheInput)) =>
              (r.skolemizationStepName must_== "nc_skolem")
                .and(r.inputStepName must_== "a")
                .and(r.const must_== FOLConst("a"))
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
          checkDerivation(input) must_== SzsStatus.VerifiedGood
        }

        "verify proof that uses a symbol in a plain inference that is not present in the axioms or conjecture" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X), file('Problems/test4.p', a)).
            |fof(c, conjecture, ![X]: p(X), file('Problems/test4.p', c)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(i, plain, p(a), inference(instance, [status(thm)], [a])).
            |fof(nc_skolem, plain, ~p(a), inference(skolemize, [status(esa), new_symbols(skolem, [a]), skolemize(X, a)], [nc])).
            |fof(taut, plain, q | ~q, inference(taut, [status(thm)], [])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [i, nc_skolem, taut])).""".stripMargin)
          checkDerivation(input) must_== SzsStatus.VerifiedGood
        }

        "verify derivation that has skolemization step whose parent has constants that are not in an axiom or conjecture" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: p(X), file('Problems/test4.p', a)).
            |fof(c, conjecture, ![X]: p(X), file('Problems/test4.p', c)).
            |fof(nc, negated_conjecture, ?[X]: (~p(X) & (q | ~q)), inference(negated_conjecture, [status(cth)], [c])).
            |fof(i, plain, p(a), inference(instance, [status(thm)], [a])).
            |fof(nc_skolem, plain, ~p(a) & (q | ~q), inference(skolemize, [status(esa), new_symbols(skolem, [a]), skolemize(X, a)], [nc])).
            |fof(inf_p, plain, $false, inference(falsum, [status(thm)], [i, nc_skolem])).""".stripMargin)
          checkDerivation(input) must_== SzsStatus.VerifiedGood
        }

        "fail if a skolem symbol occurs in the conjecture" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
            |fof(a, axiom, ![X]: ?[Y]: p(X, Y), file('Problems/problem.p', a)).
            |fof(c, conjecture, ![X]:?[Y]: p(a(X), Y), file('Problems/problem.p', c)).
            |fof(nc, negated_conjecture, ?[X]:![Y]: ~p(a(X),Y), inference(negated_conjecture, [status(cth)], [c])).
            |fof(as, plain, ![X]: p(X, a(X)), inference(skolemize, [status(esa), new_symbols(skolem, [a]), skolemize(Y, a(X))], [a])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [as, nc])).
          """.stripMargin)
            case "/Problems/problem.p" => Right("""
            |fof(a, axiom, ![X]: ?[Y]: p(X, Y)).
            |fof(c, conjecture, ![X]: ?[Y]: p(a(X), Y)).
          """.stripMargin)
          }
          checkDerivation0("/input") must beLike {
            case SzsStatus.VerifiedBad(IncorrectSkolemization(r: SkolemSymbolIsAConstantExistingInTheInput)) => ok
          }
        }

        "allow outer skolemization deeply nested inside the formula" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              |fof(a, axiom, (![X]: ?[Y]: p(X, Y)) & (![X]: ?[Z]: q(X, Z)), file('Problems/problem.p', a)).
              |fof(c, conjecture, ![X]:?[Y]: p(X, Y), file('Problems/problem.p', c)).
              |fof(nc, negated_conjecture, ?[X]:![Y]: ~p(X,Y), inference(negated_conjecture, [status(cth)], [c])).
              |fof(as, plain, (![X]: p(X, sK0(X))) & (![X]: ?[Z]: q(X, Z)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
              |fof(cont, plain, $false, inference(falsum, [status(thm)], [as, nc])).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, (![X]: ?[Y]: p(X, Y)) & (![X]: ?[Z]: q(X, Z))).
              |fof(c, conjecture, ![X]: ?[Y]: p(X, Y)).
            """.stripMargin)
          }
          checkDerivation0("/input") must beLike {
            case SzsStatus.VerifiedGood => ok
          }
        }

        "allow outer skolemization deeply nested inside the formula even if bound variable is not uniqe" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              |fof(a, axiom, (![X]: ?[Y]: p(X, Y)) & (![X]: ?[Y]: q(X, Y)), file('Problems/problem.p', a)).
              |fof(c, conjecture, ![X]:?[Y]: p(X, Y), file('Problems/problem.p', c)).
              |fof(nc, negated_conjecture, ?[X]:![Y]: ~p(X,Y), inference(negated_conjecture, [status(cth)], [c])).
              |fof(as, plain, (![X]: ?[Y]: p(X, Y)) & (![X]: q(X, sK0(X))), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
              |fof(cont, plain, $false, inference(falsum, [status(thm)], [as, nc])).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, (![X]: ?[Y]: p(X, Y)) & (![X]: ?[Z]: q(X, Z))).
              |fof(c, conjecture, ![X]: ?[Y]: p(X, Y)).
            """.stripMargin)
          }
          checkDerivation0("/input") must beLike {
            case SzsStatus.VerifiedGood => ok
          }
        }

        "succeed on inner skolemization" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              |fof(a, axiom, ![X]: ?[Y]: ![Z]: ?[W]: p(X, Y, Z, W), file('Problems/problem.p', a)).
              |fof(c, conjecture, ![X]: ?[Y]: ![Z]: ?[W]: p(X, Y, Z, W), file('Problems/problem.p', c)).
              |fof(nc, negated_conjecture, ~(![X]: ?[Y]: ![Z]: ?[W]: p(X, Y, Z, W)), inference(negated_conjecture, [status(cth)], [c])).
              |fof(as, plain, ![X]: ?[Y]: ![Z]: p(X, Y, Z, sK0(X,Z)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(W, sK0(X, Z))], [a])).
              |fof(cont, plain, $false, inference(falsum, [status(thm)], [as, nc])).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, ![X]: ?[Y]: ![Z]: ?[W]: p(X, Y, Z, W)).
              |fof(c, conjecture, ![X]: ?[Y]: ![Z]: ?[W]: p(X, Y, Z, W)).
            """.stripMargin)
          }
          checkDerivation0("/input") must_== SzsStatus.VerifiedGood
        }

        "succeed on skolemization if skolem term depends on correct variables, but in different order" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              |fof(a, axiom, ![X]: ![Y]: ?[Z]: p(X, Y, Z), file('Problems/problem.p', a)).
              |fof(c, conjecture, ![X]: ![Y]: ?[Z]: p(X, Y, Z), file('Problems/problem.p', c)).
              |fof(nc, negated_conjecture, ~(![X]: ![Y]: ?[Z]: p(X, Y, Z)), inference(negated_conjecture, [status(cth)], [c])).
              |fof(as, plain, ![X]: ![Y]: p(X, Y, sK0(Y,X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(Y,X))], [a])).
              |fof(cont, plain, $false, inference(falsum, [status(thm)], [as, nc])).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, ![X]: ![Y]: ?[Z]: p(X, Y, Z)).
              |fof(c, conjecture, ![X]: ![Y]: ?[Z]: p(X, Y, Z)).
            """.stripMargin)
          }
          checkDerivation0("/input") must_== SzsStatus.VerifiedGood
        }

        "succeed on inner skolemization" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
            fof(a,axiom,
                ! [X] :
                ? [Y] : p(Y),
                file('Problems/problem.p',a) ).
            fof(c,conjecture,
                ? [Y] : p(Y),
                file('Problems/problem.p',c) ).
            fof(neg,negated_conjecture,
                ~ ? [Y] : p(Y),
                inference(negated_conjecture,[status(cth)],[c]) ).
            fof(sk,plain,
                ! [X] : p(sK0),
                inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0)],[a]) ).
            fof(s,plain,
                p(sK0),
                inference(instantiate,[status(thm)],[sk]) ).
            fof(bot,plain,
                $false,
                inference(consequence,[status(thm)],[neg,s]) ).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, ![X]: ?[Y]: p(Y)).
              |fof(c, conjecture, ?[Y]: p(Y)).
            """.stripMargin)
          }
          checkDerivation0("/input") must_== SzsStatus.VerifiedGood
        }

        "fail on skolemization step without parents" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              fof(a,axiom,
                  ? [Y] : p(Y),
                  file('Problems/problem.p',a) ).
              fof(c,conjecture,
                  $true,
                  file('Problems/problem.p',c) ).
              fof(neg,negated_conjecture,
                  $false,
                  inference(negated_conjecture,[status(cth)],[c]) ).
              fof(sk,plain,
                  p(sK0),
                  inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0)],[]) ).
              fof(bot,plain,
                  $false,
                  inference(consequence,[status(thm)],[neg]) ).
              """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, ?[Y]: p(Y)).
              |fof(c, conjecture, $true).
            """.stripMargin)
          }

          checkDerivation0("/input") must beLike {
            case SzsStatus.VerifiedBad(r: SkolemizationStepWithoutParent) => r.stepName must_== "sk"
          }
        }

        "fail on skolemization step with multiple parents" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              fof(a,axiom,
                  ? [Y] : p(Y),
                  file('Problems/problem.p',a) ).
              fof(c,conjecture,
                  $true,
                  file('Problems/problem.p',c) ).
              fof(neg,negated_conjecture,
                  $false,
                  inference(negated_conjecture,[status(cth)],[c]) ).
              fof(sk,plain,
                  p(sK0),
                  inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0)],[a,neg]) ).
              fof(bot,plain,
                  $false,
                  inference(consequence,[status(thm)],[neg]) ).
              """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, ?[Y]: p(Y)).
              |fof(c, conjecture, $true).
            """.stripMargin)
          }

          checkDerivation0("/input") must beLike {
            case SzsStatus.VerifiedBad(r: SkolemizationStepWithMultipleParents) =>
              (r.stepName must_== "sk").and(r.parents must_== Seq("a", "neg"))
          }

        }
      }

      "axiom file directive" in {
        "fail on axiom step without file directive" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: SourceMissing) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with a non-file source" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, unknown).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveMissing) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive, but without label to a formula" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p')).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveLabelMissing) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to non-existent file" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/nonexistent.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveFileNotFound) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to non-parsable problem file" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/invalid-tptp-syntax.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveInvalidSyntax) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to file that doesn't contain the label" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p', a0)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveFileDoesNotHaveLabel) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to formula which is not alpha-equivalent to formula in step" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test5.p', a)).
            |fof(c, conjecture, p, file('Problems/test5.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to a label which is not unique and some of the labels have different formulas" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test6.p', a)).
            |fof(c, conjecture, p, file('Problems/test6.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveFileHasMultipleFormulasWithSameLabel) => reason.stepName must_== "a"
          }
        }

        "fail on axiom step with file directive that points to formula which is not an axiom" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test7.p', a)).
            |fof(c, conjecture, p, file('Problems/test7.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveStepDoesNotMatchRole) => reason.stepName must_== "a"
          }
        }

        "verify an axiom step with correct file directive, existent label in problem file and step formula and referred to formula are alpha-equivalent" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must_== SzsStatus.VerifiedGood
        }

        "verify axiom step even if label in problem file differs from label in proof file" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c1, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c1])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).
            """.stripMargin)
          checkDerivation(input) must_== SzsStatus.VerifiedGood
        }

        "fail axiom step if there are steps with same label, even if they are equal in role and have alpha-equivalent formulas" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test8.p', a)).
            |fof(c1, conjecture, p, file('Problems/test8.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c1])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveFileHasMultipleFormulasWithSameLabel) =>
              (reason.stepName must_== "a1").and(reason.label must_== "a").and(reason.fileName must_== "Problems/test8.p")
          }
        }

        "verify axiom step if given correct absolute path" in {
          val input = InputFile.fromString(s"""
            |fof(a1, axiom, p, file('${fileDirectiveRoot}/Problems/test2.p', a)).
            |fof(c1, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c1])).
            |fof(cont, plain, $$false, inference(falsum, [status(thm)], [a1, nc])).
            """.stripMargin)
          checkDerivation(input) must_== SzsStatus.VerifiedGood
        }

        "fail if an unused axiom step has missing file directive even if derivation is otherwise correct" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(unused, axiom, q).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(r: SourceMissing) => r.stepName must_== "unused"
          }
        }
      }

      "conjecture file directive" in {
        "fail on conjecture step without file directive" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: SourceMissing) => reason.stepName must_== "c"
          }
        }

        "fail on conjecture step with a non-file source" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, unknown).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveMissing) => reason.stepName must_== "c"
          }
        }

        "fail on conjecture step with file directive, but without label to a formula" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p')).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveLabelMissing) => reason.stepName must_== "c"
          }
        }

        "fail on conjecture step with file directive that points to non-existent file" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/nonexistent.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveFileNotFound) => reason.stepName must_== "c"
          }
        }

        "fail on conjecture step with file directive that points to non-parsable problem file" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/invalid-tptp-syntax.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveInvalidSyntax) => reason.stepName must_== "c"
          }
        }

        "fail on conjecture step with file directive that points to file that doesn't contain the label" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c0)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveFileDoesNotHaveLabel) => reason.stepName must_== "c"
          }
        }

        "fail on conjecture step with file directive that points to formula which is not alpha-equivalent to formula in step" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test12.p', a)).
            |fof(c, conjecture, p, file('Problems/test12.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula) => reason.stepName must_== "c"
          }
        }

        "fail on conjecture step with file directive that points to a label which is not unique and some of the labels have different formulas" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test11.p', a)).
            |fof(c, conjecture, p, file('Problems/test11.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveFileHasMultipleFormulasWithSameLabel) => reason.stepName must_== "c"
          }
        }

        "fail on conjecture step with file directive that points to formula which is not a conjecture" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p, file('Problems/test13.p', a)).
            |fof(c, conjecture, p, file('Problems/test13.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: FileDirectiveStepDoesNotMatchRole) =>
              (reason.stepName must_== "c").and(reason.expectedRole must_== "conjecture").and(reason.actualRole must_== "axiom")
          }
        }

        "verify conjecture step if given correct absolute path" in {
          val input = InputFile.fromString(s"""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c1, conjecture, p, file('${fileDirectiveRoot}/Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c1])).
            |fof(cont, plain, $$false, inference(falsum, [status(thm)], [a1, nc])).
            """.stripMargin)
          checkDerivation(input) must_== SzsStatus.VerifiedGood
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
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[DistinctFormulasWithSameName]
          }
        }

        "fail on proof with two steps with the same name even if proof steps are equal" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[DistinctFormulasWithSameName]
          }
        }
      }

      "inference parents" in {
        "fail on proof with inference steps that form a 1-step cycle" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [cont])).""".stripMargin)
          checkDerivation(input) must beLike {
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
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason) => reason must beAnInstanceOf[InferenceCycle]
          }
        }

        "fail on proof with inference parents that does not exist in proof" in {
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a)).
            |fof(c, conjecture, p, file('Problems/test2.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont2, plain, $false, inference(falsum, [status(thm)], [nc, a])).""".stripMargin)
          checkDerivation(input) must beLike {
            case SzsStatus.VerifiedBad(reason: NonExistentStep) => reason.stepName must_== "a"
          }
        }
      }

      "unknown status" in {
        "fail verification of an empty input file" in {
          checkDerivation(InputFile.fromString("")) must beAnInstanceOf[SzsStatus.VerifiedBad]
        }

        "fail an input file without a conjecture" in {
          val input = InputFile.fromString("fof(a1, axiom, p(a) & ~p(b), file('example1_c.p',a1)).")
          checkDerivation(input) must beAnInstanceOf[SzsStatus.VerifiedBad]
        }

        "not verify an input file without a $false inference" in {
          val input = InputFile.fromString("""
            |fof(a, axiom, p(a)).
            |fof(c, conjecture, p(a)).
            |fof(nc, negated_conjecture, ~p(a), inference(negated_conjecture, [status(cth)], [c])).""".stripMargin)
          checkDerivation(input) must beAnInstanceOf[SzsStatus.VerifiedBad]
        }

        "not verify proof with invalid tptp syntax" in {
          // in the following, the dots at the end of lines are missing to get an
          // invalid tptp syntax file
          val input = InputFile.fromString("""
            |fof(a1, axiom, p, file('Problems/test2.p', a))
            |fof(c, conjecture, p, file('Problems/test2.p', c))
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c]))
            |fof(cont2, plain, $false, inference(falsum, [status(thm)], [nc, a]))""".stripMargin)
          checkDerivation(input) must beAnInstanceOf[SzsStatus.Unknown]
        }

        "not verify if input has include directives (we do not support this yet)" in {
          todo
          val input = InputFile.fromString("""
            |include('filename', [a]).
            |fof(a1, axiom, p).
            |fof(c, conjecture, p).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a1, nc])).""".stripMargin)
          checkDerivation(input) must beAnInstanceOf[SzsStatus.Unknown]
        }

        "return unknown on input with overloaded symbols" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              |fof(a, axiom, p & p(a), file('Problems/problem.p', a)).
              |fof(c, conjecture, p & p(a), file('Problems/problem.p', c)).
              |fof(nc, negated_conjecture, ~(p & (p(a))), inference(negated_conjecture, [status(cth)], [c])).
              |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, p & p(a)).
              |fof(c, conjecture, p & p(a)).
            """.stripMargin)
          }

          checkDerivation0("/input") must beLike {
            case SzsStatus.Unknown(StepsWithOverloadedSymbols(symbolName, steps)) =>
              (symbolName must_== "p").and(steps.map(_.name) must_== Set("a", "c", "nc"))
          }
        }

        "return unknown on input with overloaded symbols among different steps" in {
          given resolver: FileNameResolver = {
            case "/input" => Right("""
              |fof(a, axiom, p, file('Problems/problem.p', a)).
              |fof(c, conjecture, p(a), file('Problems/problem.p', c)).
              |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
              |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
            case "/Problems/problem.p" => Right("""
              |fof(a, axiom, p).
              |fof(c, conjecture, p(a)).
            """.stripMargin)
          }

          checkDerivation0("/input") must beLike {
            case SzsStatus.Unknown(StepsWithOverloadedSymbols(symbolName, steps)) =>
              (symbolName must_== "p").and(steps.map(_.name) must_== Set("a", "c", "nc"))
          }
        }
      }

      "fail on plain inference with esa status if inference name is not skolemize" in {
        given resolver: FileNameResolver = {
          case "/input" => Right("""
            |fof(a, axiom, p, file('Problems/problem.p', a)).
            |fof(c, conjecture, p, file('Problems/problem.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(refute, plain, $false, inference(falsum, [status(esa)], [a, nc])).
            """.stripMargin)
          case "/Problems/problem.p" => Right("""
            |fof(a, axiom, p).
            |fof(c, conjecture, p).
          """.stripMargin)
        }

        checkDerivation0("/input") must beLike {
          case SzsStatus.VerifiedBad(reason: StepWithInvalidStatus) =>
            (reason.stepName must_== "refute")
              .and(reason.actualStatuses must_== Set("esa"))
              .and(reason.validStatuses must_== Set("thm"))
        }
      }

      "fail if input has two $false proof steps, one induces a correct refutation, the other induces an incorrect refutation" in {
        given resolver: FileNameResolver = {
          case "/input" => Right("""
            |fof(a, axiom, p, file('Problems/problem.p', a)).
            |fof(c, conjecture, p, file('Problems/problem.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(refute1, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            |fof(refute2, plain, $false, inference(falsum, [status(thm)], [a])).
            """.stripMargin)
          case "/Problems/problem.p" => Right("""
            |fof(a, axiom, p).
            |fof(c, conjecture, p).
          """.stripMargin)
        }

        checkDerivation0("/input") must beLike {
          case SzsStatus.VerifiedBad(r: IncorrectInference) => r.stepName must_== "refute2"
        }
      }

      "fail on hypothesis without file directive" in {
        given resolver: FileNameResolver = {
          case "/input" => Right("""
            |fof(a, hypothesis, p).
            |fof(c, conjecture, p, file('Problems/problem.p', c)).
            |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
            |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).
            """.stripMargin)
          case "/Problems/problem.p" => Right("""
            |fof(a, axiom, p).
            |fof(c, conjecture, p).
          """.stripMargin)
        }
        checkDerivation0("/input") must beLike {
          case SzsStatus.VerifiedBad(reason: SourceMissing) => reason.stepName must_== "a"
        }
      }

      "do X on skolemization step with the same parent twice" in todo("specify")
      "succeed if input has multiple $false proof steps whose induced refutations are all correct" in todo
      "give up if input has more than one $false proof step that are roots" in todo
      "fail if input has multiple $false proof steps and one of the induced refutations is incorrect" in todo

      "fail on fof inputs with higher-order formulas" in todo
      "succeed on derivation that derives $false only from axioms" in todo
      "give up if input has more than one conjecture" in todo
      "fail on plain inference with esa status if inference name is not skolemize" in todo // bad
      "fail on fof inputs with higher-order formulas" in todo // bad
      "succeed on derivation that derives $false only from axioms" in todo // martin03
      "fail if input does not contain $false" in todo // bad

      "give up if input has more than one conjecture" in todo // bad
      "succeed if input has multiple $false proof steps, but only one of them is a root" in todo // geht noch nicht
      "give up if input has more than one $false proof step that are roots" in todo

      "do X on axiom and conjecture steps that import different files" in todo("specify") //
      "do X on an axiom with a source that only refers to another axiom" in todo("specify")
    }
  }

  spec((i: InputFile) => (r: FileNameResolver) ?=> checkTstpDerivation(i)(using r))
}

class checkTstpDerivationExampleTest extends Specification {

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

    def spec(check: InputFile => FileNameResolver ?=> SzsStatus): Fragments = {
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

    s2"""
    |checkProof1
    |${spec((i: InputFile) => (r: FileNameResolver) ?=> checkTstpDerivation(i)(using r))}
  """.stripMargin
  }
}

class TstpDerivationParserUnitTest extends mutable.Specification {
  "TstpDerivation" should {
    "handle nested inference sources" in {
      val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(inf_p, plain, p, inference(cnf, [status(thm)], [inference(normalize, [status(thm)], [a1])])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [inf_p, nc])).""".stripMargin)
      TstpDerivation.fromInputFile(input) must beRight
    }

    "succeed for input where conjecture contains universal quantifier" in {
      val input = InputFile.fromString("""
        |fof(a, axiom, ![X]: p(X)).
        |fof(c, conjecture, ![X]: p(X)).
        |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
        |fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
        |fof(axiom_instance, plain, p(sK0), inference(instance, [status(thm)], [a])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).""".stripMargin)
      TstpDerivation.fromInputFile(input) must beRight.like {
        case d =>
          (d.nonConjectureRootLabels must_=== Set("cont"))
            .and(d.nonConjectureRefutationLabels must_=== Set("cont"))
      }
    }

    "compute all roots" in {
      val input = InputFile.fromString("""
        |fof(a, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(root1, plain, $false, inference(falsum, [status(thm)], [nc, a])).
        |fof(root2, plain, ~p | q, inference(or, [status(thm)], [nc])).""".stripMargin)
      TstpDerivation.fromInputFile(input) must beRight.like {
        case d => d.nonConjectureRootLabels must_== Set("root1", "root2")
      }
    }

    "include axioms in rootLabels if they are roots" in {
      val input = InputFile.fromString("""
        |fof(a, axiom, p).
        |fof(b, axiom, q).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(root, plain, $false, inference(falsum, [status(thm)], [nc, a])).""".stripMargin)
      TstpDerivation.fromInputFile(input) must beRight.like {
        case d => d.nonConjectureRootLabels must_== Set("root", "b")
      }
    }

    "do not include conjectures in rootLabels, even if they have no children" in {
      val input = InputFile.fromString("""
        |fof(a, axiom, $false).
        |fof(c, conjecture, p).
        |fof(root, plain, $false, inference(falsum, [status(thm)], [a])).""".stripMargin)
      TstpDerivation.fromInputFile(input) must beRight.like {
        case d => d.nonConjectureRootLabels must_== Set("root")
      }
    }

    "compute all refutation labels" in {
      val input = InputFile.fromString("""
        |fof(a, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(refute1, plain, $false, inference(falsum, [status(thm)], [nc, a])).
        |fof(refute2, plain, $false, inference(falsum, [status(thm)], [nc, a])).""".stripMargin)
      TstpDerivation.fromInputFile(input) must beRight.like {
        case d => d.nonConjectureRefutationLabels must_== Set("refute1", "refute2")
      }
    }

    "do not include conjecture in refutation labels even if it is $false" in {
      val input = InputFile.fromString("""
        |fof(a, axiom, $false).
        |fof(c, conjecture, $false).""".stripMargin)
      TstpDerivation.fromInputFile(input) must beRight.like {
        case d => d.nonConjectureRefutationLabels must_== Set("a")
      }
    }

    "work for a derivation that is not a refutation" in todo
    "do X if no conjecture is given" in todo
    "do X if multiple conjectures are given" in todo
    "fail if given derivation which ends in a conjecture" in todo

    "parse skolemization steps" in {
      def simpleSkolemConstantDerivation(skolemizationStep: String) = InputFile.fromString(s"""
      |fof(a, axiom, ![X]: p(X)).
      |fof(c, conjecture, ![X]: p(X)).
      |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
      |$skolemizationStep
      |fof(axiom_instance, plain, p(sK0), inference(instance, [status(thm)], [a])).
      |fof(cont, plain, $$false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).
      """.stripMargin)

      "parse skolemization step" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc]))."
        )
        TstpDerivation.fromInputFile(input) must beRight.like {
          case derivation => derivation.get("nc_skolemized") must beSome[TstpDerivationStep].like {
              case s: TstpSkolemizationStep => {
                (s.newSkolemSymbol must_=== FOLConst("sK0"))
                  .and(s.contextVariables must_=== Seq.empty)
                  .and(s.skolemizedSymbol must_=== FOLVar("X"))
              }
            }
        }
      }

      "fail on skolemization step without new_symbols(skolem, _)" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), skolemize(X, sK0)], [nc]))."
        )
        TstpDerivation.fromInputFile(input) must beLeft
      }

      "fail on skolemization step with multiple new_symbols(skolem, _)" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), new_symbols(skolem, [sK1]), skolemize(X, sK0), skolemize(X, sK1)], [nc]))."
        )
        TstpDerivation.fromInputFile(input) must beLeft
      }

      "fail on skolemization with new_symbols that is not a constant" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0(X)]), skolemize(X, sK0)], [nc]))."
        )
        TstpDerivation.fromInputFile(input) must beLeft.like {
          case _: CannotHandleInput => ok
        }
      }

      // only for now. we don't handle multiple symbols yet
      "fail on skolemization step with more than one given symbol" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0, sK1]), skolemize(X, sK0)], [nc]))."
        )
        TstpDerivation.fromInputFile(input) must beLeft.like {
          case _: CannotHandleInput => ok
        }
      }

      "fail on skolemization step without given symbol" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, []), skolemize(X, sK0)], [nc]))."
        )
        TstpDerivation.fromInputFile(input) must beLeft
      }

      "fail on skolemization step with no parents" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], []))."
        )
        TstpDerivation.fromInputFile(input) must beLeft
      }

      "fail on skolemization step with multiple parents" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc, a]))."
        )
        TstpDerivation.fromInputFile(input) must beLeft
      }

      "fail on skolemization step with differing new_symbols and skolemize terms" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK1)], [nc]))."
        )
        TstpDerivation.fromInputFile(input) must beLeft {
          (x: TstpDerivationError) => x must beAnInstanceOf[SkolemizationStepWithNewSymbolDifferingFromSkolemizeTerm]
        }
      }

      "fail on skolemization step without skolemize(_,_)" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0])], [nc]))."
        )
        TstpDerivation.fromInputFile(input) must beLeft {
          (x: TstpDerivationError) => x must beAnInstanceOf[SkolemizationStepWithoutBinding]
        }
      }

      "fail on skolemization step with multiple skolemize(_,_)" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0), skolemize(X, sK1)], [nc]))."
        )
        TstpDerivation.fromInputFile(input) must beLeft {
          (x: TstpDerivationError) => x must beAnInstanceOf[UnexpectedInput]
        }
      }

      "parse skolemization symbol with context symbols" in {
        val input = InputFile.fromString("""
        |fof(a, axiom, ![X]: p(X, a)).
        |fof(c, conjecture, ?[Y]: ![X]: p(X, Y)).
        |fof(nc, negated_conjecture, ![Y]: ?[X]: ~p(X, Y), inference(negated_conjecture, [status(cth)], [c])).
        |fof(nc_skolemized, plain, ![Y]: ~p(sK0(Y), Y), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0(Y))], [nc])).
        |fof(axiom_instance, plain, p(sK0(a), a), inference(instance, [status(thm)], [a])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).
        """.stripMargin)
        TstpDerivation.fromInputFile(input) must beRight.like {
          case derivation => derivation.get("nc_skolemized") must beSome[TstpDerivationStep].like {
              case s: TstpSkolemizationStep => {
                (s.newSkolemSymbol must_=== FOLFunctionConst("sK0", 1))
                  .and(s.contextVariables must_=== Seq(FOLVar("Y")))
                  .and(s.skolemizedSymbol must_=== FOLVar("X"))
              }
            }
        }
      }

      "parse skolemization symbol with multiple context symbols" in {
        val input = InputFile.fromString("""
        |fof(a, axiom, ![X]: p(X, a, b)).
        |fof(c, conjecture, ?[Y, Z]: ![X]: p(X, Y, Z)).
        |fof(nc, negated_conjecture, ![Y, Z]: ?[X]: ~p(X, Y, Z), inference(negated_conjecture, [status(cth)], [c])).
        |fof(nc_skolemized, plain, ![Y, Z]: ~p(sK0(Y, Z), Y, Z), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0(Y, Z))], [nc])).
        |fof(axiom_instance, plain, p(sK0(a, b), a, b), inference(instance, [status(thm)], [a])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).
        """.stripMargin)
        TstpDerivation.fromInputFile(input) must beRight.like {
          case derivation => derivation.get("nc_skolemized") must beSome[TstpDerivationStep].like {
              case s: TstpSkolemizationStep => {
                (s.newSkolemSymbol must_=== FOLFunctionConst("sK0", 2))
                  .and(s.contextVariables must_=== Seq(FOLVar("Y"), FOLVar("Z")))
                  .and(s.skolemizedSymbol must_=== FOLVar("X"))
              }
            }
        }
      }

      "should parse skolemize step where order of context variables doesn't match, but they are equal as sets" in {
        val input = InputFile.fromString("""
        |fof(a, axiom, ![X]: p(X, a, b)).
        |fof(c, conjecture, ?[Y, Z]: ![X]: p(X, Y, Z)).
        |fof(nc, negated_conjecture, ![Y, Z]: ?[X]: ~p(X, Y, Z), inference(negated_conjecture, [status(cth)], [c])).
        |fof(nc_skolemized, plain, ![Y, Z]: ~p(sK0(Y, Z), Y, Z), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0(Z, Y))], [nc])).
        |fof(axiom_instance, plain, p(sK0(b, a), a, b), inference(instance, [status(thm)], [a])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).
        """.stripMargin)
        TstpDerivation.fromInputFile(input) must beRight.like {
          case derivation => derivation.get("nc_skolemized") must beSome[TstpDerivationStep].like {
              case s: TstpSkolemizationStep => {
                (s.newSkolemSymbol must_=== FOLFunctionConst("sK0", 2))
                  .and(s.contextVariables must_=== Seq(FOLVar("Z"), FOLVar("Y")))
                  .and(s.skolemizedSymbol must_=== FOLVar("X"))
              }
            }
        }
      }

      "fail on skolemize with skolem term that has non variable arguments" in {
        val input = InputFile.fromString("""
        |fof(a, axiom, ![X]: p(X, a)).
        |fof(c, conjecture, ?[Y]: ![X]: p(X, Y)).
        |fof(nc, negated_conjecture, ![Y]: ?[X]: ~p(X, Y), inference(negated_conjecture, [status(cth)], [c])).
        |fof(nc_skolemized, plain, ![Y]: ~p(sK0(Y), Y), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0(a))], [nc])).
        |fof(axiom_instance, plain, p(sK0(a), a), inference(instance, [status(thm)], [a])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).
        """.stripMargin)
        TstpDerivation.fromInputFile(input) must beLeft {
          (x: TstpDerivationError) => x must beAnInstanceOf[UnexpectedInput]
        }
      }

      "return cannot handle input on introduced choice_axiom" in {
        val input = InputFile.fromString("""
        |fof(a, axiom, ![X]: p(X, a)).
        |fof(c, conjecture, ?[Y]: ![X]: p(X, Y)).
        |fof(nc, negated_conjecture, ![Y]: ?[X]: ~p(X, Y), inference(negated_conjecture, [status(cth)], [c])).
        |fof(ca, plain, ![Y]: (?[X]: ~p(X, Y) => ~p(sK0(Y), Y)), introduced(choice_axiom,[])).
        |fof(nc_skolemized, plain, ![Y]: ~p(sK0(Y), Y), inference(skolemization, [status(esa), new_symbols(skolem, [sK0])], [nc, ca])).
        |fof(axiom_instance, plain, p(sK0(a), a), inference(instance, [status(thm)], [a])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).
        """.stripMargin)
        TstpDerivation.fromInputFile(input) must beLeft.like {
          case x: CannotHandleInput => x.stepName must_=== "ca"
        }
      }
    }

    "skolemization" in {
      "fail on skolemization step in which the bound variable does not occur in the parent formula" in {
        val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: ?[Y]: p(X, Y)).
            |fof(s, plain, ![X]: p(X, sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(X))], [a])).
          """.stripMargin)
        val derivation = TstpDerivation.fromInputFile(input).toOption.get
        tstpDerivationToProofContext(derivation) must beLeft
      }

      "succeed on skolemization step in which the bound variable occurs in an inner existential quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y, Z]: p(X, Y, Z)).
          |fof(s, plain, ![X]: ?[Y]: p(X, Y, sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(X))], [a])).
        """.stripMargin)
        val derivation = TstpDerivation.fromInputFile(input).toOption.get
        tstpDerivationToProofContext(derivation) must beRight
      }

      "succeed on skolemization step that has no existential quantifier (but a strong universal)" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ~(![Y]: p(X,Y))).
          |fof(s, plain, ![X]: ~p(X,sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beRight
      }

      "fail on skolemization step in which the bound variable does not correspond to an existential quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: p(X,Y)).
          |fof(s, plain, ![X]: p(X,Y), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0)], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft
      }

      "fail on skolemization step in which the variable is not bound to an existential quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: p(X,Y)).
          |fof(s, plain, ![X]: p(X,sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0)], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft
      }

      "fail on skolemization step in which the variable is bound to an universal quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X, Y]: p(X,Y)).
          |fof(s, plain, ![X]: p(X,sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft
      }

      "fail on skolemization step where the resulting formula is not the skolemization of the parent formula" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: p(X,Y)).
          |fof(s, plain, ![X]: ~p(X,sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft
      }

      "fail on skolemization step whose actual context variables do not match the claimed context variables" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: ![Z]: p(X,Y,Z)).
          |fof(s, plain, ![X, Z]: p(X,sK0(X,Z), Z), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X,Z))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft
      }

      "succeed on skolemization step which claims the same context variables as the parent formula, but in a different order" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X, Y]: ?[Z]: p(X,Y,Z)).
          |fof(s, plain, ![X, Y]: p(X,Y,sK0(Y,X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(Y,X))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beRight
      }

      "fail on skolemization step with non-distinct context variables" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X, X]: ?[Y]: p(Y)).
          |fof(s, plain, ![X, X]: p(sK(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft.like {
          case IncorrectSkolemization(e: NonRectifiedFormula) =>
            (e.stepName must_== "s").and(e.formula must_== fof"!x!x?y p(y)")
          case IncorrectSkolemization(e: NoStrongQuantifierFittingSkolemization) =>
            (e.stepName must_== "s")
          case _ =>
            ko
        }
      }

      "fail on skolemization step with skolem term that uses the same context variable multiple times" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X, Y]: ?[Z]: p(X,Y,Z)).
          |fof(s, plain, ![X, Y]: p(X,Y,sK0(X,Y)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(X,X))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft.like {
          case IncorrectSkolemization(e: ContextVariableMismatch)                => e.stepName must_== "s"
          case IncorrectSkolemization(e: NoStrongQuantifierFittingSkolemization) => e.stepName must_== "s"
          case IncorrectSkolemization(e: NonRectifiedFormula)                    => e.stepName must_== "s"
        }
      }

      "fail on skolemization step which contains a context variable that does not occur in the parent formula" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X, Y]: ?[Z]: p(X,Y,Z)).
          |fof(s, plain, ![X, Y]: p(X,Y,sK0(X,Y)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(X,W))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft
      }

      "fail on skolemization step that introduces a symbol that is already used in input" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: p(X,Y,a(X))).
          |fof(s, plain, ![X]: p(X, a(X), a(X)), inference(skolemize, [status(esa), new_symbols(skolem, [a]), skolemize(Y, a(X))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft.like {
          case IncorrectSkolemization(e: SkolemSymbolIsAConstantExistingInTheInput) => ok
        }
      }

      "fail on skolemization steps which introduce the same symbol name, even if not used in parent" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ?[X]: p(X)).
          |fof(b, axiom, ?[X]: q(X)).
          |fof(s1, plain, p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [a])).
          |fof(s2, plain, q(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [b])).
          |fof(s, plain, p(sK0) & q(sK0), inference(and, [status(thm)], [s1, s2])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft.like {
          case IncorrectSkolemization(e: MultipleIncompatibleSkolemDefinitionsOfSameSymbol) => {
            (e.skolemSymbol must_== "sK0")
              .and(e.stepDefinitions.size must_== 2)
              .and(e.stepDefinitions("s1").skolemSymbol must_== FOLConst("sK0"))
              .and(e.stepDefinitions("s2").skolemSymbol must_== FOLConst("sK0"))
              .and(e.stepDefinitions("s1").skolemDefinition must_=== le"?x p(x)")
              .and(e.stepDefinitions("s2").skolemDefinition must_=== le"?x q(x)")
          }
        }
      }

      "fail on skolemization steps which introduce the same symbol name, even if they have different arity" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ?[X]: p(X)).
          |fof(b, axiom, ![Y]: ?[X]: q(Y, X)).
          |fof(s1, plain, p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [a])).
          |fof(s2, plain, ![Y]: q(Y, sK0(Y)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0(Y))], [b])).
          |fof(s, plain, p(sK0) & ![Y]: q(Y, sK0(Y)), inference(and, [status(thm)], [s1, s2])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft.like {
          case IncorrectSkolemization(e: MultipleIncompatibleSkolemDefinitionsOfSameSymbol) => {
            (e.skolemSymbol must_== "sK0")
              .and(e.stepDefinitions("s1").skolemSymbol must_== FOLConst("sK0"))
              .and(e.stepDefinitions("s2").skolemSymbol must_== FOLFunctionConst("sK0", 1))
              .and(e.stepDefinitions("s1").skolemDefinition must_=== le"?x p(x)")
              .and(e.stepDefinitions("s2").skolemDefinition must_=== le"^y ?x q(y, x)")
          }
        }
      }

      "suceed on skolemization step that introduces a symbol that is used in derivation in an unused axiom" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: p(X,Y,a(X))).
          |fof(b, axiom, ![X]: q(X, b(X))).
          |fof(s, plain, ![X]: p(X, b(X), a(X)), inference(skolemize, [status(esa), new_symbols(skolem, [b]), skolemize(Y, b(X))], [a])).
          |fof(i, plain, q(c, b(c)) & p(c, b(c), a(c)), inference(and, [status(thm)], [a, s])).
        """.stripMargin)

        TstpDerivation.fromInputFile(input) must beRight
      }

      "suceed on correct skolemization step with context variables" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ?[X]: ![Y, Z]: p(X,Y,Z)).
          |fof(c, conjecture, ?[X]: ![Y]: p(X,Y,Y)).
          |fof(nc, negated_conjecture, ![X]: ?[Z]: ~p(X,Z,Z), inference(negated_conjecture, [status(cth)], [c])).
          |fof(ncs, plain, ![X]: ~p(X, sK0(X), sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [nc])).
          |fof(as, plain, ![Y,Z]: p(sK1, Y, Z), inference(skolemize, [status(esa), new_symbols(skolem, [sK1]), skolemize(X, sK1)], [a])).
          |fof(i, plain, $false, inference(and, [status(thm)], [as, ncs])).
        """.stripMargin)

        TstpDerivation.fromInputFile(input) must beRight
      }
    }

    "fail import if given root label is not present" in todo
    "do X if axiom does not contain file source" in todo
    "do X if given root label is an axiom" in todo
    "do X if given root label is a conjecture" in todo
    "fail if derivation contains constants with different arities" in todo
  }
}

class tstpDerivationToProofContextTest extends mutable.Specification with SequentMatchers {
  import QuantifierType.*
  "FindSkolemizableInstance" should {
    "correctly detect strong quantifier instances in ∀x (P(x) → ∀x Q(x))" in {
      val f1 = fof"∀x (P(x) → ∀x Q(x))"
      val f1s = fof"∀x (P(x) → Q(c))"
      val x = fov"x"
      val c = hoc"c:i"
      val t = fot"c"
      val res1 = FindSkolemizableInstance(f1, f1s, Positive, x, c, t)
      res1 must beLike { case List(_) => ok }
      res1(0)._1 must beLike { case HOLPosition(List(1, 2)) => ok }
      res1(0)._2 must beLike { case List((Strong, y)) if y == x => ok }

      val f2s = fof"P(c) → ∀x Q(x)"
      val res2 = FindSkolemizableInstance(f1, f2s, Positive, x, c, t)
      res2 must beLike { case List(_) => ok }
      res2(0)._1 must beLike { case HOLPosition(Nil) => ok }
      res2(0)._2 must beLike { case List() => ok }

      val res3 = FindSkolemizableInstance(f1, f2s, Negative, x, c, t)
      res3 must beLike { case List() => ok }
    }

    "correctly detect strong quantifier instances in ∀z∀x∃y P(x,y)" in {
      val f1 = fof"∀z∀x∃y P(x,y)"
      val f1s = fof"∀z∀x P(x,f(x,z))"
      val x = fov"x"
      val y = fov"y"
      val z = fov"z"
      val f = hoc"f:i>i>i"
      val t = fot"f(x,z)"
      val res1 = FindSkolemizableInstance(f1, f1s, Negative, y, f, t)
      res1 must beLike { case List(_) => ok }
      res1(0)._1 must beLike { case HOLPosition(List(1, 1)) => ok }
      res1(0)._2 must beLike { case List((Weak, v1), (Weak, v2)) if (v1, v2) == (z, x) => ok }

    }

    "correctly detect strong quantifier instances in ∀x (∃y P(x,y) → ∃y∀x Q(x,y))" in {
      val f1 = fof"∀x (∃y P(x,y) → ∃y∀x Q(x,y))"
      val f1s = fof"∃y P(c,y) → ∃y∀x Q(x,y)"
      val x = fov"x"
      val c = hoc"c:i"
      val t = fot"c"

      val res1 = FindSkolemizableInstance(f1, f1s, Positive, x, c, t)
      res1 must beLike { case List(_) => ok }
      res1(0)._1 must beLike { case HOLPosition(List()) => ok }
      res1(0)._2 must beLike { case List() => ok }

      val f2s = fof"∀x (P(x,c) → ∃y∀x Q(x,y))"
      val y = fov"y"
      val res2 = FindSkolemizableInstance(f1, f2s, Positive, y, c, t)
      res2 must beLike { case List(_) => ok }
      res2(0)._1 must beLike { case HOLPosition(List(1, 1)) => ok }
      res2(0)._2 must beLike { case List((Strong, x)) => ok }

      val f3s = fof"∀x (∃y P(x,y) → ∃y Q(s(y),y))"
      val s = hoc"s:i>i"
      val t2 = fot"s(y)"

      val res3 = FindSkolemizableInstance(f1, f3s, Positive, x, s, t2)
      res3 must beLike { case List(_) => ok }
      res3(0)._1 must beLike { case HOLPosition(List(1, 2, 1)) => ok }
      res3(0)._2 must beLike { case List((Strong, u), (QuantifierType.Weak, v)) if (u, v) == (x, y) => ok }
    }

    "correctly identify the polarity of a formula" in {
      val parentFormula = fof"¬ ¬ P(x,y)"
      FindSkolemizableInstance.polarityAndContextAt(HOLPosition(List(1)), parentFormula, Negative)._1 must_== Positive
      FindSkolemizableInstance.polarityAndContextAt(HOLPosition(List(1, 1)), parentFormula, Negative)._1 must_== Negative
    }
  }

  "CreateSkolemizationProof" should {
    "Create a skolemization proof for a ∀x∃y P(x,y) / ∀x P(x,f(x))" in {
      val unskolemized = fof"∀x∃y P(x,y)"
      val skolemized = fof"∀x P(x,f(x))"
      val skTerm = fot"f(x)"
      val y = fov"y"
      val pos = HOLPosition(List(1))
      val p = CreateSkolemizationProof(unskolemized, skolemized, y, skTerm, fof"P(x,y)", pos, Negative)
      p.endSequent must_== fos"$unskolemized :- $skolemized"
    }

    "Create a skolemization proof for a ∀x ¬∀y P(x,y) / ∀x ¬P(x,f(x))" in {
      val unskolemized = fof"∀x ¬ ∀y P(x,y)"
      val skolemized = fof"∀x ¬ P(x,f(x))"
      val skTerm = fot"f(x)"
      val y = fov"y"
      val pos = HOLPosition(List(1, 1))
      val p = CreateSkolemizationProof(unskolemized, skolemized, y, skTerm, fof"P(x,y)", pos, Negative)
      p.endSequent must_== fos"$unskolemized :- $skolemized"
    }

    "Create a skolemization proof for a ∀x ¬¬ ∃y P(x,y) / ∀x ¬¬P(x,f(x))" in {
      val unskolemized = fof"∀x ¬ ¬ ∃y P(x,y)"
      val skolemized = fof"∀x ¬ ¬ P(x,f(x))"
      val skTerm = fot"f(x)"
      val y = fov"y"
      val pos = HOLPosition(List(1, 1, 1))
      val p = CreateSkolemizationProof(unskolemized, skolemized, y, skTerm, fof"P(x,y)", pos, Negative)
      p.endSequent must_== fos"$unskolemized :- $skolemized"
    }

    "Create a skolemization proof for a ∀x∃y P(x,y) / ∀z P(z,f(z))" in {
      skipped("not sure if that should work")
      val unskolemized = fof"∀x∃y P(x,y)"
      val skolemized = fof"∀z P(z,f(z))"
      val skTerm = fot"f(x)"
      val y = fov"y"
      val pos = HOLPosition(List(1))
      val p = CreateSkolemizationProof(unskolemized, skolemized, y, skTerm, fof"P(x,y)", pos, Negative)
      p.endSequent must_== fos"$unskolemized :- $skolemized"
    }

    "Create a skolemization proof for a ∀x(∀y P(x,y) → Q(x)) / ∀x (P(x,f(x)) → Q(x))" in {
      val unskolemized = fof" ∀x(∀y P(x,y) → Q(x))"
      val skolemized = fof"∀x (P(x,f(x)) → Q(x))"
      val skTerm = fot"f(x)"
      val y = fov"y"
      val pos = HOLPosition(List(1, 1))
      val p = CreateSkolemizationProof(unskolemized, skolemized, y, skTerm, fof"P(x,y)", pos, Negative)
      p.endSequent must_== fos"$unskolemized :- $skolemized"
    }

    "Create a skolemization proof for a ∀x(((¬R(x) ∧ ∃y P(x,y)) → Q(x)) → Q(x)) / ∀x(((¬R(x) ∧ P(x,s(x))) → Q(x)) → Q(x))" in {
      val unskolemized = fof" ∀x(((¬R(x) ∧ ∃y P(x,y)) → Q(x)) → Q(x))"
      val skolemized = fof" ∀x(((¬R(x) ∧ P(x,s(x))) → Q(x)) → Q(x))"
      val skTerm = fot"s(x)"
      val y = fov"y"
      val pos = HOLPosition(List(1, 1, 1, 2))
      val p = CreateSkolemizationProof(unskolemized, skolemized, y, skTerm, fof"P(x,y)", pos, Negative)
      p.endSequent must_== fos"$unskolemized :- $skolemized"
    }
  }

  "tstpDerivationToProofContext" should {
    "return proof with negated conjecture in antecedent" in {
      val input = InputFile.fromString("""
      |fof(a, axiom, ![X]: p(X)).
      |fof(c, conjecture, ![X]: p(X)).
      |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
      |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).""".stripMargin)
      val derivation = TstpDerivation.fromInputFile(input).get

      val context = withTimeout(1.second) { tstpDerivationToProofContext(derivation, Escargot) }

      context must beRight.like { context =>
        val proof = ProofLink("cont")(using context)
        context.check(proof)
        proof.conclusion.multiSetEquals(fos"!x p(x), -(!x p(x)) :- ${Bottom()}")
      }
    }

    "return proof with conjecture in succeedent" in {
      val input = InputFile.fromString("""
      |fof(a, axiom, ![X]: p(X)).
      |fof(c, conjecture, p(a)).
      |fof(end, plain, p(a), inference(instance, [status(thm)], [a])).""".stripMargin)
      val derivation = TstpDerivation.fromInputFile(input).get

      val context = withTimeout(1.second) { tstpDerivationToProofContext(derivation) }

      context must beRight.like { context =>
        val proof = ProofLink("end")(using context)
        context.check(proof)
        proof.conclusion.multiSetEquals(fos"!x p(x) :- p(a)")
      }
    }

    // this more faithfully represents the TPTP derivation
    "should return multiple axioms in antecedent if they are used multiple times" in {
      val input = InputFile.fromString("""
      |fof(a1, axiom, ![X]: p(X)).
      |fof(c, conjecture, ![X]: p(X)).
      |fof(end, plain, ![X]: p(X), inference(instance, [status(thm)], [a1, a1])).""".stripMargin)
      val derivation = TstpDerivation.fromInputFile(input).get

      val context = withTimeout(1.second) { tstpDerivationToProofContext(derivation, Escargot) }

      context must beRight.like { context =>
        val proof = ProofLink("end")(using context)
        context.check(proof)
        proof.conclusion.multiSetEquals(fos"!x p(x), !x p(x) :- !x p(x)")
      }
    }

    "work on example1_c" in {
      val input = ClasspathInputFile("proover_competition/Proofs/correct_example1_c_proof.p")
      val derivation = TstpDerivation.fromInputFile(input).toOption.get

      val context = withTimeout(1.second) { tstpDerivationToProofContext(derivation, Escargot) }

      context must beRight.like { context =>
        val proof = ProofLink("f1")(using context)
        context.check(proof)
        proof.conclusion.multiSetEquals(fos"p(a) & ~p(b), -(?x -(p(x) -> !y p(y))) :- ${Bottom()}")
      }
    }

    "work on example2_c" in {
      val derivationFile = ClasspathInputFile("proover_competition/Proofs/correct_example2_c_proof.p")
      val derivation = TstpDerivation.fromInputFile(derivationFile).get

      val context = withTimeout(1.second) { tstpDerivationToProofContext(derivation, Escargot) }

      context must beRight.like { context =>
        val proof = ProofLink("s5")(using context)
        context.check(proof)
        proof.conclusion.multiSetEquals(fos"!x(p(x) -> p(f(x))), !x(p(x) -> p(f(x))), p(a), -p(f(f(a))), -p(f(f(a))) :- ${Bottom()}")
      }
    }

    "skolemization proof" in {
      "returns skolemization proof for correct skolemization step without context variables" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ?[X]: p(X)).
            |fof(c, conjecture, ?[X]: p(X)).
            |fof(nc, negated_conjecture, ![X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(s, plain, p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [a])).
            |fof(i, plain, ~p(sK0), inference(instance, [status(thm)], [nc])).
            |fof(f, plain, $false, inference(falsum, [status(thm)], [s, i])).
        """.stripMargin
        )
        val derivation = TstpDerivation.fromInputFile(input).get
        tstpDerivationToProofContext(derivation) must beRight
      }

      "succeeds on derivation that ends in a formula containing a skolem symbol without context variables" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ?[X]: p(X)).
            |fof(s, plain, p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [a])).
        """.stripMargin
        )
        val derivation = TstpDerivation.fromInputFile(input).toOption.get
        tstpDerivationToProofContext(derivation) must beRight
      }

      "succeeds on derivation that ends in a formula containing a skolem symbol with context variables" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ![X]: ?[Y]: p(X, Y)).
            |fof(s, plain, ![X]: p(X, sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin
        )
        val derivation = TstpDerivation.fromInputFile(input).toOption.get
        tstpDerivationToProofContext(derivation) must beRight
      }

      "fails if two skolemizations with the same symbol happen even if they are on the same formula" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ![X]: p(X)).
            |fof(c, conjecture, ![X]: p(X)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(ncs1, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
            |fof(ncs2, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
            |fof(ai, plain, p(sK0), inference(instance, [status(thm)], [a])).
            |fof(i, plain, $false, inference(and, [status(thm)], [ai, ncs1, ncs2])).
        """.stripMargin
        )

        val derivation = TstpDerivation.fromInputFile(input).toOption.get
        tstpDerivationToProofContext(derivation) must beLeft.like {
          case IncorrectSkolemization(MultipleIncompatibleSkolemDefinitionsOfSameSymbol(skolemSymbol, stepDefinitions)) =>
            (skolemSymbol must_=== "sK0")
              .and(stepDefinitions must haveSize(2))
              .and(stepDefinitions("ncs1").skolemSymbol must_=== FOLFunctionConst("sK0", 0))
              .and(stepDefinitions("ncs2").skolemSymbol must_=== FOLFunctionConst("sK0", 0))
        }
      }

      "fails if two skolemization steps have incompatible definitions" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ![X]: p(X)).
            |fof(a2, axiom, ?[X]: q(X)).
            |fof(c, conjecture, ![X]: p(X)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(ncs1, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
            |fof(ncs2, plain, q(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [a2])).
            |fof(ai, plain, p(sK0), inference(instance, [status(thm)], [a, ncs2])).
            |fof(i, plain, $false, inference(and, [status(thm)], [ai, ncs1, ncs2])).
        """.stripMargin
        )

        val derivation = TstpDerivation.fromInputFile(input).toOption.get
        tstpDerivationToProofContext(derivation) must beLeft.like {
          case IncorrectSkolemization(MultipleIncompatibleSkolemDefinitionsOfSameSymbol(skolemSymbol, stepDefinitions)) =>
            (skolemSymbol must_=== "sK0")
              .and(stepDefinitions must haveSize(2))
              .and(stepDefinitions("ncs1").skolemSymbol must_== FOLConst("sK0"))
              .and(stepDefinitions("ncs2").skolemSymbol must_== FOLConst("sK0"))
              .and(stepDefinitions("ncs1").skolemDefinition must_=== le"?x ~p(x)")
              .and(stepDefinitions("ncs2").skolemDefinition must_=== le"?x q(x)")
        }
      }

      "fails if two skolemization steps have the same symbols, even if they have different arities" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ![X]: p(X)).
            |fof(a2, axiom, ![Y]: ?[X]: q(X)).
            |fof(c, conjecture, ![X]: p(X)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(ncs1, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
            |fof(ncs2, plain, ![Y]: q(sK0(Y)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0(Y))], [a2])).
            |fof(ai, plain, p(sK0), inference(instance, [status(thm)], [a])).
            |fof(i, plain, $false, inference(and, [status(thm)], [ai, ncs1, ncs2])).
        """.stripMargin
        )

        val derivation = TstpDerivation.fromInputFile(input).toOption.get
        tstpDerivationToProofContext(derivation) must beLeft.like {
          case IncorrectSkolemization(MultipleIncompatibleSkolemDefinitionsOfSameSymbol(skolemSymbol, stepDefinitions)) =>
            (skolemSymbol must_=== "sK0")
              .and(stepDefinitions must haveSize(2))
              .and(stepDefinitions("ncs1").skolemSymbol must_=== FOLFunctionConst("sK0", 0))
              .and(stepDefinitions("ncs2").skolemSymbol must_=== FOLFunctionConst("sK0", 1))
              .and(stepDefinitions("ncs1").skolemDefinition must_=== le"?x ~p(x)")
              .and(stepDefinitions("ncs2").skolemDefinition must_=== le"^y ?x q(x)")
        }
      }

      "succeeds if two skolemizations with distinct symbols happen, even if they are on the same formula" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ![X]: p(X)).
            |fof(c, conjecture, ![X]: p(X)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(ncs1, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
            |fof(ncs2, plain, ~p(sK1), inference(skolemize, [status(esa), new_symbols(skolem, [sK1]), skolemize(X, sK1)], [nc])).
            |fof(ai, plain, p(sK0) | p(sK1), inference(instances, [status(thm)], [a])).
            |fof(i, plain, $false, inference(and, [status(thm)], [ai, ncs1, ncs2])).
        """.stripMargin
        )

        val derivation = TstpDerivation.fromInputFile(input).toOption.get
        tstpDerivationToProofContext(derivation) must beRight
      }

      "picks outermost bound variable to skolemize if there are multiple with the same name" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ![X]: ?[Y]: ?[Y]: p(X, Y)).
            |fof(s, plain, ![X]: ?[Y]: p(X, Y), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin
        )
        val derivation = TstpDerivation.fromInputFile(input).get
        tstpDerivationToProofContext(derivation) must beRight
      }

      "succeed on input where a skolemization step introduces symbol that is used in plain inference, but not in conjecture or axiom" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ![X]: p(X)).
            |fof(c, conjecture, ![X]: p(X)).
            |fof(p, plain, p(c) | ~p(c), inference(tautology, [status(thm)], [])).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(ncs, plain, ~p(c), inference(skolemize, [status(esa), new_symbols(skolem, [c]), skolemize(X, c)], [nc])).
            |fof(ai, plain, p(c), inference(instance, [status(thm)], [a])).
            |fof(end, plain, $false, inference(inf, [status(thm)], [p, ncs, ai])).
        """.stripMargin
        )
        val derivation = TstpDerivation.fromInputFile(input).get
        tstpDerivationToProofContext(derivation) must beRight
      }

      "succeeds on skolemization step whose claimed formula is not equal, but alpha-equivalent to expected skolemized formula" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ?[Y]:![X]: p(Y, X)).
            |fof(c, conjecture, ?[Y]:![X]: p(Y, X)).
            |fof(nc, negated_conjecture, ![Y]:?[X]: ~p(Y, X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(ncs, plain, ![Z]: ~p(Z, sK0(Z)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0(Y))], [nc])).
            |fof(ai, plain, $false, inference(instance, [status(thm)], [a, ncs])).
        """.stripMargin
        )
        val derivation = TstpDerivation.fromInputFile(input).get
        tstpDerivationToProofContext(derivation) must beRight
      }
    }
  }
}

class acyclicityTest extends mutable.Specification {
  "isCyclic" should {
    "return false on empty graph" in {
      isCyclic(Set(), Map()) must beFalse
    }
    "return false on single node unconnected graph" in {
      isCyclic(Set(1), Map().withDefaultValue(Set.empty)) must beFalse
    }
    "return true on single node connected graph" in {
      isCyclic(Set(1), Map(1 -> Set(1))) must beTrue
    }
    "return false on two node acyclic grpah" in {
      isCyclic(Set(1, 2), Map(1 -> Set(2)).withDefaultValue(Set.empty)) must beFalse
    }
    "return true on two node acyclic graph" in {
      isCyclic(Set(1, 2), Map(1 -> Set(2), 2 -> Set(1))) must beTrue
    }
    "return false on acyclic non-connected graph" in {
      isCyclic(Set(1, 2, 3, 4), Map(1 -> Set(2), 3 -> Set(4)).withDefaultValue(Set.empty)) must beFalse
    }
    "return true on 3-step cycle" in {
      isCyclic(Set(1, 2, 3), Map(1 -> Set(2), 2 -> Set(3), 3 -> Set(1))) must beTrue
    }
    "return false on graph that is cyclic as undirected graph" in {
      isCyclic(Set(1, 2, 3, 4), Map(1 -> Set(2, 3), 2 -> Set(4), 3 -> Set(4)).withDefaultValue(Set.empty)) must beFalse
    }
  }
}
