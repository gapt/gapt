package at.logic.testing.tstp

import at.logic.proofs.algorithms.herbrandExtraction.extractExpansionSequent
import at.logic.proofs.expansionTrees._
import at.logic.cli.GAPScalaInteractiveShellLibrary.loadProver9LKProof
import at.logic.proofs.lk.algorithms.containsEqualityReasoning
import at.logic.provers.minisat._
import at.logic.provers.veriT._
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

class TstpProver9ImportValidation extends Specification {
  "TSTP Prover9 proof import and validaton" should {
    for (file <- recursiveListFiles("testing/TSTP/prover9") if file.getName.endsWith(".out")) {
      s"${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan(2 minute) {
          val p = loadProver9LKProof( file.getAbsolutePath )
          val E = extractExpansionSequent( p, false )
          val deep = toDeep( E )
          if ( containsEqualityReasoning( p ))
            (new VeriTProver).isValid( deep ) must beTrue
          else
            (new MiniSATProver).isValid( deep ) must beTrue
          ok
        }
      }
    }
  }
}
