package gapt.formats.verit

import gapt.formats.ClasspathInputFile
import gapt.formats.verit.alethe.AletheProof
import org.specs2.mutable._

class VeriTParsingTest extends Specification {

  "The veriT parser" should {

    "parse empty proof" in {
      val input =
        """
          |unsat
          |""".stripMargin
      val Some(proof) = VeriTParser.parseProof(input): @unchecked
      proof must_== AletheProof(Nil)
    }

    "parse satisfiability statement" in {
      val input =
        """
          |sat
          |Formula is Satisfiable
          |""".stripMargin
      VeriTParser.parseProof(input) must beNone
    }
  }
}
