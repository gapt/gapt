package at.logic.testing.verit

import at.logic.calculi.expansionTrees._
import at.logic.parsing.veriT.VeriTParser
import at.logic.provers.minisat._
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

class SmtLibVeritImportValidation extends Specification {
  "SMT-LIB VeriT proof import and validation" should {
    for (file <- recursiveListFiles("testing/veriT-SMT-LIB") if file.getName.endsWith(".proof_flat")) {
      file.getName in {
        skipIfRunsLongerThan(2 minute) {
          val E = VeriTParser.getExpansionProof(file.getAbsolutePath)
          E.isDefined must beTrue
          val deep = toDeep( E.get ).toFormula
          (new MiniSATProver).isValid( deep ) must beTrue
          ok
        }  
      }
    }
  }
}

