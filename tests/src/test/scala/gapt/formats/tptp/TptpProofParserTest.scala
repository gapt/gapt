package gapt.formats.tptp

import gapt.formats.ClasspathInputFile
import gapt.proofs.Clause
import gapt.proofs.resolution.{ResolutionToExpansionProof, ResolutionToLKProof, fixDerivation}
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.provers.escargot.Escargot
import org.specs2.mutable._
import org.specs2.specification.core.Fragments
import gapt.formats.InputFile

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

  "RootedTptpDerivaiton" should {
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
