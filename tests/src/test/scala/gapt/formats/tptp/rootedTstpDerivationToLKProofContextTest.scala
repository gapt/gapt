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
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.hol.HOLPosition
import gapt.formats.tptp.FindSkolemizableInstance.QuantifierType.{Strong, Weak}
import gapt.logic.Polarity.{Positive, Negative}

class rootedTstpDerivationIntoLKProofContextTest extends Specification with SequentMatchers {
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
      res3(0)._2 must beLike { case List((Strong, u), (Weak, v)) if (u, v) == (x, y) => ok }
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
      val pos = HOLPosition(List(1,1))
      val p = CreateSkolemizationProof(unskolemized, skolemized, y, skTerm, fof"P(x,y)", pos, Negative)
      p.endSequent must_== fos"$unskolemized :- $skolemized"
    }

    "Create a skolemization proof for a ∀x(((¬R(x) ∧ ∃y P(x,y)) → Q(x)) → Q(x)) / ∀x(((¬R(x) ∧ P(x,s(x))) → Q(x)) → Q(x))" in {
      val unskolemized = fof" ∀x(((¬R(x) ∧ ∃y P(x,y)) → Q(x)) → Q(x))"
      val skolemized = fof" ∀x(((¬R(x) ∧ P(x,s(x))) → Q(x)) → Q(x))"
      val skTerm = fot"s(x)"
      val y = fov"y"
      val pos = HOLPosition(List(1,1,1,2))
      val p = CreateSkolemizationProof(unskolemized, skolemized, y, skTerm, fof"P(x,y)", pos, Negative)
      p.endSequent must_== fos"$unskolemized :- $skolemized"
    }
  }

  "rootedTstpDerivationIntoLKProof" should {
    "return proof with negated conjecture in antecedent" in {
      val input = InputFile.fromString(
        """
          |fof(a, axiom, ![X]: p(X)).
          |fof(c, conjecture, ![X]: p(X)).
          |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
          |fof(cont, plain, $false, inference(falsum, [status(thm)], [a, nc])).""".stripMargin)
      val sketch = RootedTstpDerivation.fromInputFileAndRootLabel(input, "cont").toOption.get

      val lkProof = withTimeout(1.second) {
        rootedTstpDerivationToLKProofContext(sketch, Escargot)
      }

      lkProof must beRight.like { (proof, context) =>
        context.check(proof)
        proof.conclusion.multiSetEquals(fos"!x p(x), -(!x p(x)) :- ${Bottom()}")
      }
    }

    "return proof with conjecture in succeedent" in {
      val input = InputFile.fromString(
        """
          |fof(a, axiom, ![X]: p(X)).
          |fof(c, conjecture, p(a)).
          |fof(end, plain, p(a), inference(instance, [status(thm)], [a])).""".stripMargin)
      val sketch = RootedTstpDerivation.fromInputFileAndRootLabel(input, "end").toOption.get

      val lkProof = withTimeout(1.second) {
        rootedTstpDerivationToLKProofContext(sketch, Escargot)
      }

      lkProof must beRight.like { (proof, context) =>
        context.check(proof)
        proof.conclusion.multiSetEquals(fos"!x p(x) :- p(a)")
      }
    }

    // this more faithfully represents the TPTP derivation
    "should return multiple axioms in antecedent if they are used multiple times" in {
      val input = InputFile.fromString(
        """
          |fof(a1, axiom, ![X]: p(X)).
          |fof(c, conjecture, ![X]: p(X)).
          |fof(end, plain, ![X]: p(X), inference(instance, [status(thm)], [a1, a1])).""".stripMargin)
      val sketch = RootedTstpDerivation.fromInputFileAndRootLabel(input, "end").toOption.get

      val lkProof = withTimeout(1.second) {
        rootedTstpDerivationToLKProofContext(sketch, Escargot)
      }

      lkProof must beRight.like { (proof, context) =>
        context.check(proof)
        proof.conclusion.multiSetEquals(fos"!x p(x), !x p(x) :- !x p(x)")
      }
    }

    "work on example1_c" in {
      val input = ClasspathInputFile("proover_competition/Proofs/correct_example1_c_proof.p")
      val sketch = RootedTstpDerivation.fromInputFileRefutation(input).toOption.get

      val lkProof = withTimeout(1.second) {
        rootedTstpDerivationToLKProofContext(sketch, Escargot)
      }

      lkProof must beRight.like { (proof, context) =>
        context.check(proof)
        proof.conclusion.multiSetEquals(fos"p(a) & ~p(b), -(?x -(p(x) -> !y p(y))) :- ${Bottom()}")
      }
    }

    "work on example2_c" in {
      val input = ClasspathInputFile("proover_competition/Proofs/correct_example2_c_proof.p")
      val sketch = RootedTstpDerivation.fromInputFileRefutation(input).toOption.get

      val lkProof = withTimeout(1.second) {
        rootedTstpDerivationToLKProofContext(sketch, Escargot)
      }

      lkProof must beRight.like { (proof, context) =>
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
        """.stripMargin)
        val derivation = RootedTstpDerivation.fromInputFileAndRootLabel(input, "f").get
        rootedTstpDerivationToLKProofContext(derivation) must beRight
      }

      "succeeds on derivation that ends in a formula containing a skolem symbol without context variables" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ?[X]: p(X)).
            |fof(s, plain, p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [a])).
        """.stripMargin)
        val derivation = RootedTstpDerivation.fromInputFileAndRootLabel(input, "s").toOption.get
        rootedTstpDerivationToLKProofContext(derivation) must beRight
      }

      "succeeds on derivation that ends in a formula containing a skolem symbol with context variables" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ![X]: ?[Y]: p(X, Y)).
            |fof(s, plain, ![X]: p(X, sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val derivation = RootedTstpDerivation.fromInputFileAndRootLabel(input, "s").toOption.get
        rootedTstpDerivationToLKProofContext(derivation) must beRight
      }

      "succeeds if two skolemizations with the same symbol happen if they are on the same formula" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ![X]: p(X)).
            |fof(c, conjecture, ![X]: p(X)).
            |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(ncs1, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
            |fof(ncs2, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
            |fof(ai, plain, p(sK0), inference(instance, [status(thm)], [a])).
            |fof(i, plain, $false, inference(and, [status(thm)], [ai, ncs1, ncs2])).
        """.stripMargin)

        val derivation = RootedTstpDerivation.fromInputFileRefutation(input).toOption.get
        rootedTstpDerivationToLKProofContext(derivation) must beRight
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
        """.stripMargin)

        val derivation = RootedTstpDerivation.fromInputFileRefutation(input).toOption.get
        rootedTstpDerivationToLKProofContext(derivation) must beLeft.like {
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
        """.stripMargin)

        val derivation = RootedTstpDerivation.fromInputFileRefutation(input).toOption.get
        rootedTstpDerivationToLKProofContext(derivation) must beLeft.like {
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
        """.stripMargin)

        val derivation = RootedTstpDerivation.fromInputFileRefutation(input).toOption.get
        rootedTstpDerivationToLKProofContext(derivation) must beRight
      }

      "picks outermost bound variable to skolemize if there are multiple with the same name" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ![X]: ?[Y]: ?[Y]: p(X, Y)).
            |fof(s, plain, ![X]: ?[Y]: p(X, Y), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val derivation = RootedTstpDerivation.fromInputFileAndRootLabel(input, "s").get
        rootedTstpDerivationToLKProofContext(derivation) must beRight
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
        """.stripMargin)
        val derivation = RootedTstpDerivation.fromInputFileRefutation(input).get
        rootedTstpDerivationToLKProofContext(derivation) must beRight
      }

      "succeeds on skolemization step whose claimed formula is not equal, but alpha-equivalent to expected skolemized formula" in {
        val input = InputFile.fromString(
          """
            |fof(a, axiom, ?[Y]:![X]: p(Y, X)).
            |fof(c, conjecture, ?[Y]:![X]: p(Y, X)).
            |fof(nc, negated_conjecture, ![Y]:?[X]: ~p(Y, X), inference(negated_conjecture, [status(cth)], [c])).
            |fof(ncs, plain, ![Z]: ~p(Z, sK0(Z)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0(Y))], [nc])).
            |fof(ai, plain, $false, inference(instance, [status(thm)], [a, ncs])).
        """.stripMargin)
        val derivation = RootedTstpDerivation.fromInputFileRefutation(input).get
        rootedTstpDerivationToLKProofContext(derivation) must beRight
      }
    }
  }
}
