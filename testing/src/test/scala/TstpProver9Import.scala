package at.logic.testing.tstp

import at.logic.cli.GAPScalaInteractiveShellLibrary.loadProver9LKProof
import at.logic.testing.{skipIfRunsLongerThan, recursiveListFiles}
import org.specs2.mutable._

class TstpProver9Import extends Specification {
  "TSTP Prover9 proof import" should {
    for (file <- recursiveListFiles("testing/TSTP/prover9") if file.getName.endsWith(".out")) {
      s"${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan(1 minute) {
          loadProver9LKProof(file.getAbsolutePath)
          ok
        }
      }
    }
  }
}