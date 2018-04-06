package gapt.formats.leancop

import gapt.formats.ClasspathInputFile
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class LeanCoPParserTest extends Specification with SatMatchers {

  "irrationals" in {
    LeanCoPParser.getExpansionProof( ClasspathInputFile( "irrationals.leancop.s" ) ) must beLike {
      case Some( expansion ) =>
        expansion.deep must beEValidSequent
    }
  }

}
