package gapt.integration_tests

import gapt.examples._
import gapt.proofs.Sequent
import gapt.proofs.expansion.{ eliminateMerges, findMerges }
import gapt.provers.eprover.EProver
import gapt.provers.prover9.Prover9
import org.specs2.mutable._

class nTapeTest extends Specification {
  args( skipAll = !Prover9.isInstalled )
  "The higher-order tape proof" should {
    "do cut-elimination on the 2 copies tape proof tape3.llk" in {
      val acnf_lkconclusion = nTape2.acnf.conclusion
      //println( nTape2.preprocessed_input_proof.conclusion )
      //println( acnf_lkconclusion )
      acnf_lkconclusion.multiSetEquals( nTape2.preprocessed_input_proof.conclusion ) must beTrue

      nTape2.thf_reproving_deep( None ) must be_!=( "" )

      ok( "acnf could be created" )
    }

    "collect statistics of the 2 copies tape proof, including reproving the deep formula (tape3.llk)" in {
      if ( !EProver.isInstalled ) skipped( "No EProver installed!" )
      nTape2.collectStatistics()
      nTapeInstances.computeInstances( nTape2.expansion_proof, nTape2.proofdb().Definitions )
      ok( "all statistics created!" )
    }

    "do cut-elimination on the 1 copy tape proof tape3ex.llk" in {
      val acnf_lkconclusion = nTape3.acnf.conclusion
      acnf_lkconclusion.multiSetEquals( nTape3.preprocessed_input_proof.conclusion ) must beTrue
      nTape3.thf_reproving_deep( None ) must be_!=( "" )

      ok( "acnf could be created" )
    }

    "print statistics of the 3 copies tape proof, including reproving the deep formula tape3ex.llk" in {
      if ( !EProver.isInstalled ) skipped( "No EProver installed!" )
      nTape3.collectStatistics()
      nTapeInstances.computeInstances( nTape3.expansion_proof, nTape3.proofdb().Definitions )
      ok( "all statistics created!" )
    }

    "calculate of the css for version 4 of the n-tape proof" in {
      for ( i <- 2 to 4 ) nTape4( i ).preprocessed_css_hol_clauses
      ok( "computations done" )
    }

    "calulate the css for version 5 of the n-tape proof" in {
      for ( i <- 2 to 4 ) nTape5( i ).preprocessed_css_hol_clauses
      ok( "computations done" )
    }

    "calulate the css for version 5 with arithmetical if-then-else of the n-tape proof" in {
      nTape5Arith( 2 ).preprocessed_css_hol_clauses
      ok( "computations done" )
    }

    "evaluate the formulas in the if-then-else tests" in {
      nTape6.sequents
      ok( "terms created" )
    }

    "eliminateMerge removes all merges in n3Tape proof" in {
      val merge_nodes =
        findMerges( nTape3.expansion_proof )

      merge_nodes must beEmpty
    }

  }

}
