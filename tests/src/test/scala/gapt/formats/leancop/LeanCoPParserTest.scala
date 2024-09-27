package gapt.formats.leancop

import gapt.expr._
import gapt.formats.ClasspathInputFile
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification
import gapt.proofs.expansion.RichExpansionSequent

class LeanCoPParserTest extends Specification with SatMatchers {

  "parse universally quantified formula" in {
    LeanCoPParser.parseAll(LeanCoPParser.quantified, "! [_X, _Y] : ('P'(_X, _Y))") match {
      case LeanCoPParser.Success(f, _) =>
        f must_== fof"!x !y #c(P:i>i>o)(x,y)"
      case _ => failure
    }
    ok
  }

  "parse existentially quantified formula" in {
    LeanCoPParser.parseAll(LeanCoPParser.quantified, "? [_X, _Y] : ('P'(_X, _Y))") match {
      case LeanCoPParser.Success(f, _) =>
        f must_== fof"?x ?y #c(P:i>i>o)(x,y)"
      case _ => failure
    }
    ok
  }

  "irrationals" in {
    LeanCoPParser.getExpansionProof(ClasspathInputFile("irrationals.leancop.s")) must beLike {
      case Some(expansion) =>
        expansion.deep must beEValidSequent
    }
  }

}
