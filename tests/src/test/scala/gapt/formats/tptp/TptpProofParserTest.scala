package gapt.formats.tptp

import gapt.formats.ClasspathInputFile
import gapt.proofs.Clause
import gapt.proofs.resolution.{ResolutionToExpansionProof, ResolutionToLKProof, fixDerivation}
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.provers.escargot.Escargot
import org.specs2.mutable._
import org.specs2.specification.core.Fragments
import gapt.formats.InputFile
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.stringInterpolationForExpressions

class TptpProofParserTest extends Specification {

  Fragments.foreach(Seq(
    "RNG103+2_E---1.9.THM-CRf.s",
    "ALG011-1_Metis---2.3.UNS-CRf.s",
    "GEO008-3_iprover-1.4.tptp",
    "LCL101-1_Vampire---4.0.UNS-REF.s",
    "SYN728-1_VampireZ3---1.0.UNS-Ref.s",
    "HEN005-6_SPASS-3.7.UNS-Ref.s",
    "counting-cnf.vampire.tptp"
  )) { fn =>
    fn in {
      val (endSequent, sketch) = TptpProofParser.parse(ClasspathInputFile(fn))
      sketch.conclusion must_== Clause()

      val Right(robinson) = RefutationSketchToResolution(sketch): @unchecked
      robinson.conclusion must_== Clause()

      val fixed = fixDerivation(robinson, endSequent)

      // not converting that one to LK because it takes too long
      if (fn != "RNG103+2_E---1.9.THM-CRf.s")
        ResolutionToLKProof(fixed)

      val expansion = ResolutionToExpansionProof(fixed)
      Escargot.isValid(expansion.deep) must_== true
    }
  }
}

class TptpProofParserUnitTest extends Specification {
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
  }

  "RootedTstpDerivation" should {
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
        RootedTstpDerivation.fromInputFileRefutation(input) must beRight.like {
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
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft
      }

      "fail on skolemization step with multiple new_symbols(skolem, _)" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), new_symbols(skolem, [sK1]), skolemize(X, sK0), skolemize(X, sK1)], [nc]))."
        )
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft
      }

      "fail on skolemization with new_symbols that is not a constant" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0(X)]), skolemize(X, sK0)], [nc]))."
        )
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft.like {
          case _: CannotHandleInput => ok
        }
      }

      // only for now. we don't handle multiple symbols yet
      "fail on skolemization step with more than one given symbol" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0, sK1]), skolemize(X, sK0)], [nc]))."
        )
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft.like {
          case _: CannotHandleInput => ok
        }
      }

      "fail on skolemization step without given symbol" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, []), skolemize(X, sK0)], [nc]))."
        )
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft
      }

      "fail on skolemization step with no parents" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], []))."
        )
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft
      }

      "fail on skolemization step with multiple parents" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc, a]))."
        )
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft
      }

      "fail on skolemization step with differing new_symbols and skolemize terms" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK1)], [nc]))."
        )
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft {
          (x: TstpDerivationImportError) => x must beAnInstanceOf[SkolemizationStepWithNewSymbolDifferingFromSkolemizeTerm]
        }
      }

      "fail on skolemization step without skolemize(_,_)" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0])], [nc]))."
        )
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft {
          (x: TstpDerivationImportError) => x must beAnInstanceOf[SkolemizationStepWithoutBinding]
        }
      }

      "fail on skolemization step with multiple skolemize(_,_)" in {
        val input = simpleSkolemConstantDerivation(
          "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0), skolemize(X, sK1)], [nc]))."
        )
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft {
          (x: TstpDerivationImportError) => x must beAnInstanceOf[UnexpectedInput]
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
        RootedTstpDerivation.fromInputFileRefutation(input) must beRight.like {
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
        RootedTstpDerivation.fromInputFileRefutation(input) must beRight.like {
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
        RootedTstpDerivation.fromInputFileRefutation(input) must beRight.like {
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
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft {
          (x: TstpDerivationImportError) => x must beAnInstanceOf[UnexpectedInput]
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
        RootedTstpDerivation.fromInputFileRefutation(input) must beLeft.like {
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

      "fail on skolemization step in which the bound variable occurs in an inner existential quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ?[Y, Z]: p(X, Y, Z)).
          |fof(s, plain, ![X]: ?[Y]: p(X, Y, sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(X))], [a])).
        """.stripMargin)
        val derivation = TstpDerivation.fromInputFile(input).toOption.get
        tstpDerivationToProofContext(derivation) must beLeft
      }

      "fail on skolemization step that has no outermost existential quantifier" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X]: ~(![Y]: p(X,Y))).
          |fof(s, plain, ![X]: ~p(X,sK0(X)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Y, sK0(X))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft
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
        tstpDerivationToProofContext(derivation) must beLeft
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
        }
      }

      "fail on skolemization step with skolem term that uses the same context variable multiple times" in {
        val input = InputFile.fromString("""
          |fof(a, axiom, ![X, Y]: ?[Z]: p(X,Y,Z)).
          |fof(s, plain, ![X, Y]: p(X,Y,sK0(X,Y)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(X,X))], [a])).
        """.stripMargin)
        val Right(derivation) = TstpDerivation.fromInputFile(input): @unchecked
        tstpDerivationToProofContext(derivation) must beLeft.like {
          case IncorrectSkolemization(e: ContextVariableMismatch) => e.stepName must_== "s"
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

        RootedTstpDerivation.fromInputFileAndRootLabel(input, "s") must beRight
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

        RootedTstpDerivation.fromInputFileRefutation(input) must beRight
      }
    }

    "fail import if given root label is not present" in todo
    "do X if axiom does not contain file source" in todo
    "do X if given root label is an axiom" in todo
    "do X if given root label is a conjecture" in todo
    "fail if derivation contains constants with different arities" in todo
  }
}

class acyclicityTest extends Specification {
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
