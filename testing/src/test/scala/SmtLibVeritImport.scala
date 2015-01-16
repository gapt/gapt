package at.logic.testing.verit

import at.logic.parsing.veriT.VeriTParser
import at.logic.testing.{skipIfRunsLongerThan, recursiveListFiles}
import org.specs2.mutable._

class SmtLibVeritImport extends Specification {
  "SMT-LIB VeriT proof import" should {
    for (file <- recursiveListFiles("testing/veriT-SMT-LIB") if file.getName.endsWith(".proof_flat")) {
      file.getName in {
        skipIfRunsLongerThan(1 minute) {
          VeriTParser.getExpansionProof(file.getAbsolutePath)
          ok
        }
      }
    }
  }
}