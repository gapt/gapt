package at.logic.gapt.formats.leancop

import java.io.InputStreamReader

import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class LeanCoPParserTest extends Specification with SatMatchers {

  "irrationals" in {
    LeanCoPParser.getExpansionProof( new InputStreamReader(
      getClass.getClassLoader.getResourceAsStream( "irrationals.leancop.s" )
    ) ) must beLike {
      case Some( expansion ) =>
        expansion.deep must beEValidSequent
    }
  }

}
