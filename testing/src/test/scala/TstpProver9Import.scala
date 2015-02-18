package at.logic.testing.tstp

import at.logic.gapt.proofs.lk.algorithms
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary.loadProver9LKProof
import at.logic.gapt.proofs.lk.algorithms.containsEqualityReasoning
import at.logic.gapt.provers.minisat._
import at.logic.gapt.provers.veriT._
import at.logic.testing.{skipIfRunsLongerThan, recursiveListFiles}
import at.logic.gapt.proofs.algorithms.herbrandExtraction._
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
