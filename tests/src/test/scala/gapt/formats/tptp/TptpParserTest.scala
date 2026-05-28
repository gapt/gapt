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
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations.source must_== InferenceRecord(
        "abc",
        Seq(TptpTerm("status", FOLConst("thm"))),
        Seq(ParentInfo("a", None))
      )
    }
  }
}
