package gapt.formats.tptp

import gapt.expr.formula.Bottom
import gapt.expr.stringInterpolationForExpressions
import gapt.formats.ClasspathInputFile
import gapt.formats.InputFile
import gapt.formats.tptp.RootedTstpDerivation
import gapt.proofs.SequentMatchers
import gapt.provers.escargot.Escargot
import gapt.utils.EitherHelpers.RichEither
import gapt.utils.withTimeout
import org.specs2.mutable.Specification

import scala.concurrent.duration.*

class rootedTstpDerivationIntoLKProofTest extends Specification with SequentMatchers {
  "rootedTstpDerivationIntoLKProof" should {
    "return proof with negated conjecture in antecedent" in {
      val input = InputFile.fromString("""
      |fof(a, axiom, ![X]: p(X)).
      |fof(c, conjecture, ![X]: p(X)).
      |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
      |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).""".stripMargin)
      val sketch = RootedTstpDerivation.fromInputFileAndRootLabel(input, "cont").toOption.get

      val lkProof = withTimeout(1.second) { rootedTstpDerivationToLKProof(sketch, Escargot) }

      lkProof must beRight.like { proof => proof.conclusion.multiSetEquals(fos"!x p(x), -(!x p(x)) :- ${Bottom()}") }
    }

    "return proof with conjecture in succeedent" in {
      val input = InputFile.fromString("""
      |fof(a, axiom, ![X]: p(X)).
      |fof(c, conjecture, p(a)).
      |fof(end, plain, p(a), inference(instance, [status(thm)], [a])).""".stripMargin)
      val sketch = RootedTstpDerivation.fromInputFileAndRootLabel(input, "end").toOption.get

      val lkProof = withTimeout(1.second) { rootedTstpDerivationToLKProof(sketch, Escargot) }

      lkProof must beRight.like { proof => proof.conclusion.multiSetEquals(fos"!x p(x) :- p(a)") }
    }

    // this more faithfully represents the TPTP derivation
    "should return multiple axioms in antecedent if they are used multiple times" in {
      val input = InputFile.fromString("""
      |fof(a1, axiom, ![X]: p(X)).
      |fof(c, conjecture, ![X]: p(X)).
      |fof(end, plain, ![X]: p(X), inference(instance, [status(thm)], [a1, a1])).""".stripMargin)
      val sketch = RootedTstpDerivation.fromInputFileAndRootLabel(input, "end").toOption.get

      val lkProof = withTimeout(1.second) { rootedTstpDerivationToLKProof(sketch, Escargot) }

      lkProof must beRight.like { proof =>
        proof.conclusion.multiSetEquals(fos"!x p(x), !x p(x) :- !x p(x)")
      }
    }

    "work on example1_c" in {
      val input = ClasspathInputFile("proover_competition/Proofs/correct_example1_c_proof.p")
      val sketch = RootedTstpDerivation.fromInputFileRefutation(input).toOption.get

      val lkProof = withTimeout(1.second) { rootedTstpDerivationToLKProof(sketch, Escargot) }

      lkProof must beRight.like { proof =>
        proof.conclusion.multiSetEquals(fos"p(a) & ~p(b), -(?x -(p(x) -> !y p(y))) :- ${Bottom()}")
      }
    }

    "work on example2_c" in {
      val input = ClasspathInputFile("proover_competition/Proofs/correct_example2_c_proof.p")
      val sketch = RootedTstpDerivation.fromInputFileRefutation(input).toOption.get

      val lkProof = withTimeout(1.second) { rootedTstpDerivationToLKProof(sketch, Escargot) }

      lkProof must beRight.like { proof =>
        proof.conclusion.multiSetEquals(fos"!x(p(x) -> p(f(x))), !x(p(x) -> p(f(x))), p(a), -p(f(f(a))), -p(f(f(a))) :- ${Bottom()}")
      }
    }

    "should fail on examples" in todo

    "skolemization proof" in {
      "returns skolemization proof for correct skolemization step without context variables" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ?[X]: p(X)).
          |fof(c, conjecture, ?[X]: p(X)).
          |fof(nc, negated_conjecture, ![X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
          |fof(s, plain, p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [a])).
          |fof(i, plain, ~p(sK0), inference(instance, [status(thm)], [nc])).
          |fof(f, plain, $false, inference(falsum, [status(thm)], [s, i])).
        """.stripMargin)
        val derivation = RootedTstpDerivation.fromInputFileAndRootLabel(input, "f").get
        rootedTstpDerivationToLKProof(derivation) must beRight
      }

      "fails on incorrect proof that ends in a formula containing a skolem symbol without context variables" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ?[X]: p(X)).
          |fof(s, plain, p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [a])).
        """.stripMargin)
        val derivation = RootedTstpDerivation.fromInputFileAndRootLabel(input, "s").toOption.get
        rootedTstpDerivationToLKProof(derivation) must beLeft.like {
          case d => d must beAnInstanceOf[DeskolemizationFailed]
        }
      }

      "fails on incorrect proof that ends in a formula containing a skolem symbol with context variables" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: p(X, Y)).
          |fof(s, plain, ![X]: p(X, sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val derivation = RootedTstpDerivation.fromInputFileAndRootLabel(input, "s").toOption.get
        rootedTstpDerivationToLKProof(derivation) must beLeft.like {
          case d => d must beAnInstanceOf[DeskolemizationFailed]
        }
      }
    }
  }
}
