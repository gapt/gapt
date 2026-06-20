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
  "TptpDerivation" should {
    "handle nested inference sources" in {
      val input = InputFile.fromString("""
        |fof(a1, axiom, p).
        |fof(c, conjecture, p).
        |fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
        |fof(inf_p, plain, p, inference(cnf, [status(thm)], [inference(normalize, [status(thm)], [a1])])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [inf_p, nc])).""".stripMargin)
      TptpDerivation.fromInputFile(input) must beRight
    }

    "succeed for input where conjecture contains universal quantifier" in {
      val input = InputFile.fromString("""
        |fof(a, axiom, ![X]: p(X)).
        |fof(c, conjecture, ![X]: p(X)).
        |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
        |fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, sK0), skolemize(X, sK0)], [nc])).
        |fof(axiom_instance, plain, p(sK0), inference(instance, [status(thm)], [a])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).""".stripMargin)
      TptpDerivation.fromInputFile(input) must beRight
    }

    "work for a derivation that is not a refutation" in todo
    "do X if no conjecture is given" in todo
    "do X if multiple conjectures are given" in todo
    "fail if given derivation which ends in a conjecture" in todo
  }

  "RootedTptpDerivation" should {
    def simpleSkolemConstantDerivation(skolemizationStep: String) = InputFile.fromString(
      s"""
      |fof(a, axiom, ![X]: p(X)).
      |fof(c, conjecture, ![X]: p(X)).
      |fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
      |$skolemizationStep
      |fof(axiom_instance, plain, p(sK0), inference(instance, [status(thm)], [a])).
      |fof(cont, plain, $$false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).
      """.stripMargin
    )

    "parse skolemization step" in {
      val input = simpleSkolemConstantDerivation(
        "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc]))."
      )
      RootedTptpDerivation.fromInputFileRefutation(input) must beRight.like {
        case derivation => derivation.get("nc_skolemized") must beSome[TptpDerivationStep].like {
            case TptpSkolemizationStep(name, formula, parent, newSkolemSymbol, contextVariables, skolemizedSymbol, annotations) => {
              (newSkolemSymbol must_=== FOLConst("sK0"))
                .and(contextVariables must_=== Seq.empty)
                .and(skolemizedSymbol must_=== FOLVar("X"))
            }
          }
      }
    }

    "fail on skolemization step without new_symbols(skolem, _)" in {
      val input = simpleSkolemConstantDerivation(
        "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), skolemize(X, sK0)], [nc]))."
      )
      RootedTptpDerivation.fromInputFileRefutation(input) must beLeft
    }

    "fail on skolemization step with multiple new_symbols(skolem, _)" in {
      val input = simpleSkolemConstantDerivation(
        "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), new_symbols(skolem, [sK1]), skolemize(X, sK0), skolemize(X, sK1)], [nc]))."
      )
      RootedTptpDerivation.fromInputFileRefutation(input) must beLeft
    }

    "fail on skolemization with new_symbols that is not a constant" in todo

    // only for now. we don't handle multiple symbols yet
    "fail on skolemization step with more than one given symbol" in {
      val input = simpleSkolemConstantDerivation(
        "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0, sK1]), skolemize(X, sK0)], [nc]))."
      )
      RootedTptpDerivation.fromInputFileRefutation(input) must beLeft[TptpDerivationImportError].like {
        case _: CannotHandleInput => ok
      }
    }

    "fail on skolemization step without given symbol" in {
      val input = simpleSkolemConstantDerivation(
        "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, []), skolemize(X, sK0)], [nc]))."
      )
      RootedTptpDerivation.fromInputFileRefutation(input) must beLeft
    }

    "fail on skolemization step with no parents" in {
      val input = simpleSkolemConstantDerivation(
        "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], []))."
      )
      RootedTptpDerivation.fromInputFileRefutation(input) must beLeft
    }

    "fail on skolemization step with multiple parents" in {
      val input = simpleSkolemConstantDerivation(
        "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc, a]))."
      )
      RootedTptpDerivation.fromInputFileRefutation(input) must beLeft
    }

    "fail on skolemization step with differing new_symbols and skolemize terms" in {
      val input = simpleSkolemConstantDerivation(
        "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK1)], [nc]))."
      )
      RootedTptpDerivation.fromInputFileRefutation(input) must beLeft {
        (x: TptpDerivationImportError) => x must beAnInstanceOf[SkolemizationStepWithDifferingSkolemTerms]
      }
    }

    "fail on skolemization step without skolemize(_,_)" in {
      val input = simpleSkolemConstantDerivation(
        "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0])], [nc]))."
      )
      RootedTptpDerivation.fromInputFileRefutation(input) must beLeft {
        (x: TptpDerivationImportError) => x must beAnInstanceOf[UnexpectedInput]
      }
    }

    "fail on skolemization step with multiple skolemize(_,_)" in {
      val input = simpleSkolemConstantDerivation(
        "fof(nc_skolemized, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0), skolemize(X, sK1)], [nc]))."
      )
      RootedTptpDerivation.fromInputFileRefutation(input) must beLeft {
        (x: TptpDerivationImportError) => x must beAnInstanceOf[UnexpectedInput]
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
      RootedTptpDerivation.fromInputFileRefutation(input) must beRight.like {
        case derivation => derivation.get("nc_skolemized") must beSome[TptpDerivationStep].like {
            case TptpSkolemizationStep(name, formula, parent, newSkolemSymbol, contextVariables, skolemizedSymbol, annotations) => {
              (newSkolemSymbol must_=== FOLFunctionConst("sK0", 1))
                .and(contextVariables must_=== Seq(FOLVar("Y")))
                .and(skolemizedSymbol must_=== FOLVar("X"))
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
        |fof(axiom_instance, plain, p(sK0(a), a), inference(instance, [status(thm)], [a])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).
        """.stripMargin)
      RootedTptpDerivation.fromInputFileRefutation(input) must beRight.like {
        case derivation => derivation.get("nc_skolemized") must beSome[TptpDerivationStep].like {
            case TptpSkolemizationStep(name, formula, parent, newSkolemSymbol, contextVariables, skolemizedSymbol, annotations) => {
              (newSkolemSymbol must_=== FOLFunctionConst("sK0", 2))
                .and(contextVariables must_=== Seq(FOLVar("Y"), FOLVar("Z")))
                .and(skolemizedSymbol must_=== FOLVar("X"))
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
        |fof(axiom_instance, plain, p(sK0(a), a), inference(instance, [status(thm)], [a])).
        |fof(cont, plain, $false, inference(falsum, [status(thm)], [nc_skolemized, axiom_instance])).
        """.stripMargin)
      RootedTptpDerivation.fromInputFileRefutation(input) must beRight.like {
        case derivation => derivation.get("nc_skolemized") must beSome[TptpDerivationStep].like {
            case TptpSkolemizationStep(name, formula, parent, newSkolemSymbol, contextVariables, skolemizedSymbol, annotations) => {
              (newSkolemSymbol must_=== FOLFunctionConst("sK0", 2))
                .and(contextVariables must_=== Seq(FOLVar("Z"), FOLVar("Y")))
                .and(skolemizedSymbol must_=== FOLVar("X"))
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
      RootedTptpDerivation.fromInputFileRefutation(input) must beLeft {
        (x: TptpDerivationImportError) => x must beAnInstanceOf[UnexpectedInput]
      }
    }

    "fail import if given root label is not present" in todo
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
