package at.logic.testing.verit

import java.io.File

import at.logic.parsing.veriT.VeriTParser
import at.logic.utils.executionModels.timeout.withTimeout
import org.specs2.mutable._

class SmtLibVeritImport extends Specification {
  "SMT-LIB VeriT proof import" should {
    for (file <- recursiveListFiles(new File("testing/veriT-SMT-LIB")) if file.getName.endsWith(".proof_flat")) {
      file.getName in {
        withTimeout(60 * 1000) {
          VeriTParser.getExpansionProof(file.getAbsolutePath)
          ok
        }
      }
    }
  }

  def recursiveListFiles(f: File): List[File] =
    if (f.isDirectory)
      f.listFiles.toList.flatMap(recursiveListFiles)
    else
      List(f)
}