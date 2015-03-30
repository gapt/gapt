package at.logic.testing.tstp

import at.logic.gapt.proofs.lk.algorithms
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary.loadProver9LKProof
import at.logic.gapt.proofs.lk.algorithms.{ solve, containsEqualityReasoning }
import at.logic.gapt.provers.minisat._
import at.logic.gapt.provers.veriT._
import at.logic.testing.{ skipIfRunsLongerThan, recursiveListFiles }
import at.logic.gapt.proofs.algorithms.herbrandExtraction._
import org.specs2.mutable._
import org.specs2.specification.core.Fragment
import scala.concurrent.duration._

trait Prover9TstpSpec {
  def prover9Proofs = recursiveListFiles( "testing/TSTP/prover9" ).filter( _.getName.endsWith( ".out" ) )
}

class TstpProver9Import extends Specification with Prover9TstpSpec {
  "Prover9 import" should {
    Fragment.foreach( prover9Proofs ) { file =>
      s"work for ${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan( 1 minute ) {
          loadProver9LKProof( file.getAbsolutePath )
          ok
        }
      }
    }
  }
}

class TstpProver9ImportMinisatValidation extends Specification with Prover9TstpSpec {
  "Prover9 import and minisat validaton" should {
    Fragment.foreach( prover9Proofs ) { file =>
      s"work for ${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan( 2 minute ) {
          val p_opt = try {
            Some( loadProver9LKProof( file.getAbsolutePath ) )
          } catch {
            case e: Exception => {
              skipped( "prover9 import has thrown exception." )
              None
            }
          }
          if ( containsEqualityReasoning( p_opt.get ) )
            skipped( "proof contains equality reasoning." )
          else {
            val E = extractExpansionSequent( p_opt.get, false )
            val deep = toDeep( E )
            ( new MiniSATProver ).isValid( deep ) must beTrue
          }
          ok
        }
      }
    }
  }
}

class TstpProver9ImportVeritValidation extends Specification with Prover9TstpSpec {
  "Prover9 import and veriT validaton" should {
    Fragment.foreach( prover9Proofs ) { file =>
      s"work for ${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan( 2 minute ) {
          val p_opt = try {
            Some( loadProver9LKProof( file.getAbsolutePath ) )
          } catch {
            case e: Exception => {
              skipped( "prover9 import has thrown exception." )
              None
            }
          }
          if ( !containsEqualityReasoning( p_opt.get ) )
            skipped( "proof does not contain equality reasoning." )
          else {
            val E = extractExpansionSequent( p_opt.get, false )
            val deep = toDeep( E )
            ( new VeriTProver ).isValid( deep ) must beTrue
          }
          ok
        }
      }
    }
  }
}

class TstpProver9ImportSolvePropValidation extends Specification with Prover9TstpSpec {
  "Prover9 import and solvePropositional validaton" should {
    Fragment.foreach( prover9Proofs ) { file =>
      s"work for ${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan( 2 minute ) {
          val p_opt = try {
            Some( loadProver9LKProof( file.getAbsolutePath ) )
          } catch {
            case e: Exception => {
              skipped( "prover9 import has thrown exception." )
              None
            }
          }
          if ( containsEqualityReasoning( p_opt.get ) )
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

class TstpProver9ImportExpProofToLKProofValidation extends Specification with Prover9TstpSpec {
  "Prover9 import and ExpansionProofToLKProof validaton" should {
    Fragment.foreach( prover9Proofs ) { file =>
      s"work for ${file.getParentFile.getName}/${file.getName}" in {
        skipIfRunsLongerThan( 2 minute ) {
          val p_opt = try {
            Some( loadProver9LKProof( file.getAbsolutePath ) )
          } catch {
            case e: Exception => {
              skipped( "prover9 import has thrown exception." )
              None
            }
          }
          if ( containsEqualityReasoning( p_opt.get ) )
            skipped( "proof contains equality reasoning." )
          else {
            val E = extractExpansionSequent( p_opt.get, false )
            solve.expansionProofToLKProof( E ).isDefined must beTrue
          }
          ok
        }
      }
    }
  }
}

