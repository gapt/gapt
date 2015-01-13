package at.logic.testing.tstp

import java.io.File

import at.logic.cli.GAPScalaInteractiveShellLibrary.loadProver9LKProof
import at.logic.utils.executionModels.timeout.withTimeout
import org.specs2.mutable._

class TstpProver9Import extends Specification {
  "TSTP Prover9 proof import" should {
    for (file <- recursiveListFiles(new File("testing/TSTP/prover9")) if file.getName.endsWith(".out")) {
      s"${file.getParentFile.getName}/${file.getName}" in {
        withTimeout(60 * 1000) {
          loadProver9LKProof(file.getAbsolutePath)
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