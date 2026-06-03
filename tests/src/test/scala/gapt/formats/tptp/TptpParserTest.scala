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

  def parse(input: String): TptpFile =
    TptpImporter.loadWithoutIncludes(InputFile.fromString(input))

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
      val tptpFile = parse("fof(name, plain, p, inference(abc, [status(thm)], [a])).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome
    }

    "parse absenece of annotations as None" in {
      val tptpFile = parse("fof(c, conjecture, p).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beNone
    }

    "parse rest of annotations" in {
      val tptpFile = parse("fof(name, plain, p, inference(abc, [status(thm)], [a]), [abc, xyz]).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.optionalInfo must_== Seq(TptpTerm("abc"), TptpTerm("xyz"))
      }
    }

    "parse source name" in {
      val tptpFile = parse("fof(name, plain, p, source_name).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source must_== Source.Name("source_name")
      }
    }

    "parse source name with whitespace afterwards" in {
      val tptpFile = parse("fof(name, plain, p, source_name    ).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source must_== Source.Name("source_name")
      }
    }

    "parse inference rule name" in {
      val tptpFile = parse("fof(name, plain, p, inference(rule_name, [status(thm)], [a])).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference].rule must_== "rule_name"
      }
    }

    "parse useful info" in {
      val tptpFile = parse("fof(name, plain, p, inference(rule_name, [status(thm)], [a])).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference].usefulInfo must_== Seq(TptpTerm("status", TptpTerm("thm")))
      }
    }

    "parse parent source" in {
      val tptpFile = parse("fof(name, plain, p, inference(rule_name, [status(thm)], [a])).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference].parents(0).source must_== Source.Name("a")
      }
    }

    "parse recursive parent source" in {
      val tptpFile = parse("fof(name, plain, p, inference(rule_name, [status(thm)], [a, inference(b, [status(thm)], [c])])).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference]
          .parents(1).source.asInstanceOf[Source.Inference]
          .parents(0).source.asInstanceOf[Source.Name] must_== Source.Name("c")
      }
    }

    "parse parent details" in {
      val tptpFile = parse("fof(name, plain, p, inference(rule_name, [status(thm)], [a:some_info])).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference].parents(0).details must beSome { TptpTerm("some_info") }
      }
    }

    "parse parent details as none if not given" in {
      val tptpFile = parse("fof(name, plain, p, inference(rule_name, [status(thm)], [a])).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Inference].parents(0).details must beNone
      }
    }

    "parse internal source" in {
      val tptpFile = parse("fof(name, plain, p, introduced(tautology, [], [])).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Internal].introType must_== "tautology"
      }
    }

    "parse vampire sat_splitting_component introduced" in {
      val tptpFile = parse("fof(name, plain, p, introduced(sat_splitting_component,[new_symbols(naming,[$spl18])])).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Internal].introType must_== "sat_splitting_component"
      }
    }

    "parse internal source with nested useful info" in {
      val tptpFile = parse("fof(name, plain, p, introduced(tautology,[equality,[$cnf(d(f(f(a2,a2),a1))),[0],$fot(f(a2,f(a2,a1)))]])).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Internal].usefulInfo(0) must_== TptpTerm("equality")
      }
    }

    "parse file sources" in {
      val tptpFile = parse("fof(f7,axiom,(( ! [X0,X1] : (a1(X1,s_3(X1,X0),X0) | 'D_2'(X0) | ~'D_1'(X0)) )), file('counting-cnf.tptp',sequent6)).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.File].fileName must_== "counting-cnf.tptp"
      }
    }

    "parse file info" in {
      val tptpFile = parse("fof(f7,axiom,(( ! [X0,X1] : (a1(X1,s_3(X1,X0),X0) | 'D_2'(X0) | ~'D_1'(X0)) )), file('counting-cnf.tptp',sequent6)).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.File].fileInfo must_== Some("sequent6")
      }
    }

    "parse file source without info" in {
      val tptpFile = parse("fof(f7,axiom,(( ! [X0,X1] : (a1(X1,s_3(X1,X0),X0) | 'D_2'(X0) | ~'D_1'(X0)) )), file('counting-cnf.tptp')).")
      tptpFile.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.File].fileInfo must_== None
      }
    }

    "parse theory source with name" in {
      val tptp = parse("fof(f,axiom,a=a,theory(equality)).")
      tptp.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Theory].name must_== "equality"
      }
    }

    "parse theory source with additional info" in {
      val tptp = parse("fof(f,axiom,a=a,theory(equality, [info])).")
      tptp.inputs(0).asInstanceOf[AnnotatedFormula].annotations must beSome { (a: Annotations) =>
        a.source.asInstanceOf[Source.Theory].usefulInfo(0) must_== TptpTerm("info")
      }
    }

    "not parse invalid source" in todo

    "parse integer names" in todo
    "parse single-quoted names" in todo
    "parse back-quoted names" in todo
    "not parse upper-case names" in todo

    "parse include directives" in todo

    "parse different languages" in todo
  }
}
