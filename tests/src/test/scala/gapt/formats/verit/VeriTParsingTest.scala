package gapt.formats.verit

import gapt.formats.ClasspathInputFile
import org.specs2.mutable._

class VeriTParsingTest extends Specification {

  "The veriT parser" should {

    "parse empty proof" in {
      val input =
        """
          |unsat
          |""".stripMargin
      val Some( proof ) = VeriTParser.parseProof( input )
      proof must_== AletheProof( Nil )
    }

    "parse satisfiability statement" in {
      val input =
        """
          |sat
          |Formula is Satisfiable
          |""".stripMargin
      VeriTParser.parseProof( input ) must beNone
    }
  }
}

