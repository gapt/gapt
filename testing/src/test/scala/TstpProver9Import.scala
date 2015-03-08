package at.logic.testing.tstp

import at.logic.algorithms.lk._
import at.logic.calculi.expansionTrees._
import at.logic.calculi.lk.base._
import at.logic.cli.GAPScalaInteractiveShellLibrary.loadProver9LKProof
import at.logic.provers.minisat._
import at.logic.provers.veriT._
import at.logic.testing.{skipIfRunsLongerThan, recursiveListFiles}
import at.logic.transformations.herbrandExtraction._
import org.specs2.mutable._

class TstpProver9Import extends Specification {
  "Prover9 import" should {
    for (file <- recursiveListFiles("testing/TSTP/prover9") if file.getName.endsWith(".out")) {
      s"work for ${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan(1 minute) {
          loadProver9LKProof(file.getAbsolutePath)
          ok
        }
      }
    }
  }
}

class TstpProver9ImportMinisatValidation extends Specification {
  "Prover9 import and minisat validaton" should {
    for (file <- recursiveListFiles("testing/TSTP/prover9") if file.getName.endsWith(".out")) {
      s"work for ${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan(2 minute) {
          val p_opt = try {
            Some( loadProver9LKProof( file.getAbsolutePath ))
          } catch {
            case e: Exception => { 
              skipped( "prover9 import has thrown exception." )
              None
            }
          }
          if ( containsEqualityReasoning( p_opt.get ))
            skipped( "proof contains equality reasoning." )
          else {
            val E = extractExpansionSequent( p_opt.get, false )
            val deep = toDeep( E )
            (new MiniSATProver).isValid( deep ) must beTrue
          }
          ok
        }
      }
    }
  }
}

class TstpProver9ImportVeritValidation extends Specification {
  "Prover9 import and veriT validaton" should {
    for (file <- recursiveListFiles("testing/TSTP/prover9") if file.getName.endsWith(".out")) {
      s"work for ${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan(2 minute) {
          val p_opt = try {
            Some( loadProver9LKProof( file.getAbsolutePath ))
          } catch {
            case e: Exception => {  
              skipped( "prover9 import has thrown exception." )
              None
            }
          }
          if ( !containsEqualityReasoning( p_opt.get ))
            skipped( "proof does not contain equality reasoning." )
          else {
            val E = extractExpansionSequent( p_opt.get, false )
            val deep = toDeep( E )
            (new VeriTProver).isValid( deep ) must beTrue
          }
          ok
        }
      }
    }
  }
}

class TstpProver9ImportSolvePropValidation extends Specification {
  "Prover9 import and minisat validaton" should {
    for (file <- recursiveListFiles("testing/TSTP/prover9") if file.getName.endsWith(".out")) {
      s"work for ${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan(2 minute) {
          val p_opt = try {
            Some( loadProver9LKProof( file.getAbsolutePath ))
          } catch {
            case e: Exception => {  
              skipped( "prover9 import has thrown exception." )
              None
            }
          }
          if ( containsEqualityReasoning( p_opt.get ))
            skipped( "proof contains equality reasoning." )
          else {
            val E = extractExpansionSequent( p_opt.get, false )
            val deep = toDeep( E )
            solve.solvePropositional( deep ).isDefined must beTrue
          }
          ok
        }
      }
    }
  }
}

