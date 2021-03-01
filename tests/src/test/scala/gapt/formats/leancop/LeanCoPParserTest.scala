package gapt.formats.leancop

import gapt.expr._
import gapt.expr.formula.Iff
import gapt.formats.ClasspathInputFile
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class LeanCoPParserTest extends Specification with SatMatchers {

  "parse biconditional to two implications" in {
    LeanCoPParser.parseAll( LeanCoPParser.biconditional, "'P' <=> 'Q'" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fof"P <-> Q"
      case _ => failure
    }
    ok
  }

  "parse universally quantified formula" in {
    LeanCoPParser.parseAll( LeanCoPParser.quantified, "! [_X, _Y] : ('P'(_X, _Y))" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fof"!x !y #c(P:i>i>o)(x,y)"
      case _ => failure
    }
    ok
  }

  "parse existentially quantified formula" in {
    LeanCoPParser.parseAll( LeanCoPParser.quantified, "? [_X, _Y] : ('P'(_X, _Y))" ) match {
      case LeanCoPParser.Success( f, _ ) =>
        f must_== fof"?x ?y #c(P:i>i>o)(x,y)"
      case _ => failure
    }
    ok
  }

  "irrationals" in {
    LeanCoPParser.getExpansionProof( ClasspathInputFile( "irrationals.leancop.s" ) ) must beLike {
      case Some( expansion ) =>
        expansion.deep must beEValidSequent
    }
  }

}
