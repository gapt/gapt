package gapt.formats.tptp

import org.specs2.mutable.Specification
import gapt.expr.stringInterpolationForExpressions
import gapt.formats.tptp.RootedTptpDerivation
import scala.concurrent.duration._
import gapt.expr.formula.Bottom
import gapt.provers.escargot.Escargot
import gapt.formats.InputFile
import gapt.utils.withTimeout
import gapt.formats.ClasspathInputFile

class rootedTptpDerivationIntoLKProofTest extends Specification {
  "rootedTptpDerivationIntoLKProof" should {
    "return proof with negated conjecture in antecedent" in {
      val input = InputFile.fromString("""
      |fof(a, axiom, ![X]: p(X)).
      |fof(c, conjecture, ![X]: p(X)).
      |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
      |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).""".stripMargin)
      val sketch = RootedTptpDerivation.fromInputFileAndRootLabel(input, "cont").toOption.get

      val lkProof = withTimeout(1.second) { rootedTptpDerivationToLKProof(sketch, Escargot) }

      lkProof must beRight.like { proof => proof.conclusion.multiSetEquals(fos"!x p(x), -(!x p(x)) :- ${Bottom()}") }
    }

    "return proof with conjecture in succeedent" in {
      val input = InputFile.fromString("""
      |fof(a, axiom, ![X]: p(X)).
      |fof(c, conjecture, p(a)).
      |fof(end, plain, p(a), inference(instance, [status(thm)], [a])).""".stripMargin)
      val sketch = RootedTptpDerivation.fromInputFileAndRootLabel(input, "end").toOption.get

      val lkProof = withTimeout(1.second) { rootedTptpDerivationToLKProof(sketch, Escargot) }

      lkProof must beRight.like { proof => proof.conclusion.multiSetEquals(fos"!x p(x) :- p(a)") }
    }

    // this more faithfully represents the TPTP derivation
    "should return multiple axioms in antecedent if they are used multiple times" in {
      val input = InputFile.fromString("""
      |fof(a1, axiom, ![X]: p(X)).
      |fof(c, conjecture, ![X]: p(X)).
      |fof(end, plain, ![X]: p(X), inference(instance, [status(thm)], [a1, a1])).""".stripMargin)
      val sketch = RootedTptpDerivation.fromInputFileAndRootLabel(input, "end").toOption.get

      val lkProof = withTimeout(1.second) { rootedTptpDerivationToLKProof(sketch, Escargot) }

      lkProof must beRight.like { proof =>
        proof.conclusion.multiSetEquals(fos"!x p(x), !x p(x) :- !x p(x)")
      }
    }

    "work on example1_c" in {
      val input = ClasspathInputFile("proover_competition/Proofs/correct_example1_c_proof.p")
      val sketch = RootedTptpDerivation.fromInputFileRefutation(input).toOption.get

      val lkProof = withTimeout(1.second) { rootedTptpDerivationToLKProof(sketch, Escargot) }

      lkProof must beRight.like { proof =>
        proof.conclusion.multiSetEquals(fos"p(a) & ~p(b), -(?x -(p(x) -> !y p(y))) :- ${Bottom()}")
      }
    }

    "work on example2_c" in {
      val input = ClasspathInputFile("proover_competition/Proofs/correct_example2_c_proof.p")
      val sketch = RootedTptpDerivation.fromInputFileRefutation(input).toOption.get

      val lkProof = withTimeout(1.second) { rootedTptpDerivationToLKProof(sketch, Escargot) }

      lkProof must beRight.like { proof =>
        proof.conclusion.multiSetEquals(fos"!x(p(x) -> p(f(x))), !x(p(x) -> p(f(x))), p(a), -p(f(f(a))), -p(f(f(a))) :- ${Bottom()}")
      }
    }

    "should fail on examples" in todo
  }
}
