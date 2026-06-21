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
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.SequentMatchers
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallLeftRule
import scala.util.boundary
import boundary.break
import gapt.proofs.lk.LKProof

class rootedTptpDerivationIntoLKProofTest extends Specification with SequentMatchers {
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

    "skolemization" in {
      "output skolemization proof for correct skolemization step without context variables" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ?[X]: p(X)).
          |fof(s, plain, p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [a])).
        """.stripMargin)
        val derivation = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s").toOption.get
        rootedTptpDerivationToLKProof(derivation) must beRight.like {
          case c @ CutRule(left, _, ExistsSkLeftRule(p, i, f, s), _) => {
            (c.conclusion must beMultiSetEqual(fos"?X p(X) :- p(sK0)"))
              .and(s must_=== foc"sK0")
              .and(f must_=== fof"?X p(X)")
          }
        }
      }

      "output skolemization proof for correct skolemization step with a context variable" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: p(X, Y)).
          |fof(s, plain, ![X]: p(X, sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val derivation = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s").toOption.get
        rootedTptpDerivationToLKProof(derivation) must beRight[LKProof].like { r =>
          boundary {
            val rightCut = r match {
              case CutRule(left, _, right, _) => right
              case _                          => break(ko)
            }
            val innerForAllRight = rightCut match {
              case ForallRightRule(p, _, _, _) => p
              case _                           => break(ko)
            }
            val innerForAllLeft = innerForAllRight match {
              case ForallLeftRule(p, _, _, _, _) => p
              case _                             => break(ko)
            }
            val existsSkLeft = innerForAllLeft match {
              case e: ExistsSkLeftRule => e
              case _                   => break(ko)
            }
            val ExistsSkLeftRule(p, i, introducedFormula, skolemTerm) = existsSkLeft
            (skolemTerm must_=== fot"sK0(X)")
              .and(introducedFormula must_=== fof"?Y p(X,Y)")
              .and(r.conclusion must beMultiSetEqual(fos"!X?Y p(X,Y) :- !X p(X, sK0(X))"))
          }
        }
      }

      "fail on skolemization step in which the bound variable does not occur in the parent formula" in {
        val input = InputFile.fromString("""
            |fof(a, axiom, ![X]: ?[Y]: p(X, Y)).
            |fof(s, plain, ![X]: p(X, sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(X))], [a])).
          """.stripMargin)
        val derivation = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s").toOption.get
        rootedTptpDerivationToLKProof(derivation) must beLeft
      }

      "fail on skolemization step in which the bound variable occurs in an inner existential quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y, Z]: p(X, Y, Z)).
          |fof(s, plain, ![X]: ?[Y]: p(X, Y, sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(X))], [a])).
        """.stripMargin)
        val derivation = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s").toOption.get
        rootedTptpDerivationToLKProof(derivation) must beLeft
      }

      "fail on skolemization step that has no outermost existential quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ~(![Y]: p(X,Y))).
          |fof(s, plain, ![X]: ~p(X,sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val Right(derivation) = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s"): @unchecked
        rootedTptpDerivationToLKProof(derivation) must beLeft
      }

      "fail on skolemization step in which the bound variable does not correspond to an existential quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: p(X,Y)).
          |fof(s, plain, ![X]: p(X,Y), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0)], [a])).
        """.stripMargin)
        val Right(derivation) = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s"): @unchecked
        rootedTptpDerivationToLKProof(derivation) must beLeft
      }

      "fail on skolemization step in which the variable is not bound to an existential quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: p(X,Y)).
          |fof(s, plain, ![X]: p(X,sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0)], [a])).
        """.stripMargin)
        val Right(derivation) = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s"): @unchecked
        rootedTptpDerivationToLKProof(derivation) must beLeft
      }

      "fail on skolemization step in which the variable is bound to an universal quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X, Y]: p(X,Y)).
          |fof(s, plain, ![X]: p(X,sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val Right(derivation) = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s"): @unchecked
        rootedTptpDerivationToLKProof(derivation) must beLeft
      }

      "fail on skolemization step where the resulting formula is not the skolemization of the parent formula" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: p(X,Y)).
          |fof(s, plain, ![X]: ~p(X,sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val Right(derivation) = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s"): @unchecked
        rootedTptpDerivationToLKProof(derivation) must beLeft
      }

      "fail on skolemization step whose actual context variables don't match the claimed context variables" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: ![Z]: p(X,Y,Z)).
          |fof(s, plain, ![X, Z]: p(X,sK0(X,Z)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X,Z))], [a])).
        """.stripMargin)
        val Right(derivation) = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s"): @unchecked
        rootedTptpDerivationToLKProof(derivation) must beLeft
      }

      "succeed on skolemization step which claims the same context variables as the parent formula, but in a different order" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X, Y]: ?[Z]: p(X,Y,Z)).
          |fof(s, plain, ![X, Y]: p(X,Y,sK0(Y,X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(Y,X))], [a])).
        """.stripMargin)
        val Right(derivation) = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s"): @unchecked
        rootedTptpDerivationToLKProof(derivation) must beRight
      }

      "fail on skolemization step which contains a context variable that does not occur in the parent formula" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X, Y]: ?[Z]: p(X,Y,Z)).
          |fof(s, plain, ![X, Y]: p(X,Y,sK0(X,Y)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(X,W))], [a])).
        """.stripMargin)
        val Right(derivation) = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s"): @unchecked
        rootedTptpDerivationToLKProof(derivation) must beLeft
      }

      "fail on skolemization step that introduces a symbol that is already used in parent" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: p(X,Y,a(X))).
          |fof(s, plain, ![X]: p(X, a(X), a(X)), inference(skolemize, [status(esa), new_symbols(skolem, [a]), skolemize(Y, a(X))], [a])).
        """.stripMargin)
        val Right(derivation) = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s"): @unchecked
        rootedTptpDerivationToLKProof(derivation) must beLeft
      }

      "do X on skolemization step that introduces a symbol that is used in derivation in other non-parent formula" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y]: p(X,Y,a(X))).
          |fof(b, axiom, ![X]: q(X, b(X))).
          |fof(s, plain, ![X]: p(X, b(X), a(X)), inference(skolemize, [status(esa), new_symbols(skolem, [b]), skolemize(Y, b(X))], [a])).
          |fof(i, plain, q(c, b(c)) & p(c, b(c), a(c)), inference(and, [status(thm)], [a, b])).
        """.stripMargin)
        val Right(derivation) = RootedTptpDerivation.fromInputFileAndRootLabel(input, "s"): @unchecked
        todo
      }

      "fail on skolemization steps which introduce the same symbol name" in todo
      "fail on skolemization steps which introduce the same symbol name, even if they have different arity" in todo

      "do X on skolemization step whose parent formula contains multiple bound variables with the same name" in todo
      "do X on skolemization step shose claimed formula is not equal, but alpha-equivalent to expected skolemized formula" in todo

      "fail on skolemization step if parent context variables don't match formula context variables" in todo
      "succeed on bound variables within nested forall / exists scopes" in todo

    }
  }
}
