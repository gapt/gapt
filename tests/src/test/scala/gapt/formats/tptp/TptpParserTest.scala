package gapt.formats.tptp

import gapt.formats.ClasspathInputFile
import org.specs2.mutable.Specification
import gapt.expr.formula.fol.FOLConst
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
    "import inference record" in {
      val input = "fof(name, plain, p, inference(abc, [status(thm)], [a]))."
      val tptpFile = TptpImporter.loadWithoutIncludes(InputFile.fromString(input))
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].convert.annotations must beSome { (a: Annotations) =>
        a.source must_== InferenceRecord(
          "abc",
          Seq(TptpTerm("status", FOLConst("thm"))),
          Seq(ParentInfo("a", None))
        )
      }
    }

    "import trivial proof inference record" in {
      val input = InputFile.fromString("""
      |fof(c, conjecture, $true).
      |fof(nc, negated_conjecture, $false, inference(nc, [status(cth)], [c])).""".stripMargin)
      val tptpFile = TptpImporter.loadWithoutIncludes(input)
      tptpFile.inputs(1).asInstanceOf[AnnotatedFormula].convert.annotations must beSome { (a: Annotations) =>
        a.source must_== InferenceRecord(
          "nc",
          Seq(TptpTerm("status", FOLConst("cth"))),
          Seq(ParentInfo("c", None))
        )
      }
    }

    "import absenece of annotations as None" in {
      val input = InputFile.fromString("fof(c, conjecture, p).")
      val tptpFile = TptpImporter.loadWithoutIncludes(input)
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].convert.annotations must beNone
    }

    "parse annotated formula name as name, not just string" in todo
  }
}
