package gapt.formats.tptp

import gapt.formats.ClasspathInputFile
import org.specs2.mutable.Specification
import gapt.formats.InputFile

class TptpParserTest extends Specification {

  def loadTPTP(fileName: String) =
    resolveIncludes(
      TptpFile(Seq(IncludeDirective(fileName, None))),
      fileName => TptpImporter.loadWithoutIncludes(ClasspathInputFile(fileName))
    )

  "gra014p1" in {
    loadTPTP("GRA014+1.p")
    ok
  }

  "tautological clauses" in {
    TptpProblemToResolution(loadTPTP("HWV116-1_excerpt.p"))
    ok
  }

  "TPTP parser" should {
    "parse annotations" in {
      val input = "fof(name, plain, p, inference(abc, [status(thm)], [a]))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome
    }

    "parse absenece of annotations as None" in {
      val input = InputFile.fromString("fof(c, conjecture, p).")
      val tptpFile = TptpImporter.loadWithoutIncludes(input)
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beNone
    }

    "parse rest of annotations" in {
      val input = "fof(name, plain, p, inference(abc, [status(thm)], [a]), [abc, xyz])."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.optionalInfo must_== Seq(TptpTerm("abc"), TptpTerm("xyz"))
      }
    }

    "parse source name" in {
      val input = "fof(name, plain, p, source_name)."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source must_== Source.Name("source_name")
      }
    }

    "parse source name with whitespace afterwards" in {
      val input = "fof(name, plain, p, source_name    )."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source must_== Source.Name("source_name")
      }
    }

    "parse inference rule name" in {
      val input = "fof(name, plain, p, inference(rule_name, [status(thm)], [a]))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference].rule must_== "rule_name"
      }
    }

    "parse useful info" in {
      val input = "fof(name, plain, p, inference(rule_name, [status(thm)], [a]))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference].usefulInfo must_== Seq(TptpTerm("status", TptpTerm("thm")))
      }
    }

    "parse parent source" in {
      val input = "fof(name, plain, p, inference(rule_name, [status(thm)], [a]))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference].parents(0).source must_== Source.Name("a")
      }
    }

    "parse recursive parent source" in {
      val input = "fof(name, plain, p, inference(rule_name, [status(thm)], [a, inference(b, [status(thm)], [c])]))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference]
          .parents(1).source.asInstanceOf[Source.Inference]
          .parents(0).source.asInstanceOf[Source.Name] must_== Source.Name("c")
      }
    }

    "parse parent details" in {
      val input = "fof(name, plain, p, inference(rule_name, [status(thm)], [a:some_info]))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference].parents(0).details must beSome { TptpTerm("some_info") }
      }
    }

    "parse parent details as none if not given" in {
      val input = "fof(name, plain, p, inference(rule_name, [status(thm)], [a]))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference].parents(0).details must beNone
      }
    }

    "parse internal source" in {
      val input = "fof(name, plain, p, introduced(tautology, [], []))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Internal].introType must_== "tautology"
      }
    }

    "parse vampire sat_splitting_component introduced" in {
      val input = "fof(name, plain, p, introduced(sat_splitting_component,[new_symbols(naming,[$spl18])]))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Internal].introType must_== "sat_splitting_component"
      }
    }

    "parse internal source with nested useful info" in {
      val input = "fof(name, plain, p, introduced(tautology,[equality,[$cnf(d(f(f(a2,a2),a1))),[0],$fot(f(a2,f(a2,a1)))]]))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Internal].usefulInfo(0) must_== TptpTerm("equality")
      }
    }

    "not parse invalid source" in todo

    "parse integer names" in todo
    "parse single-quoted names" in todo
    "parse back-quoted names" in todo
    "not parse upper-case names" in todo

    "parse include directives" in todo
  }
}
