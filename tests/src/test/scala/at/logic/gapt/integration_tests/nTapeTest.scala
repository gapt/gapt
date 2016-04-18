package at.logic.gapt.integration_tests

import at.logic.gapt.examples.{ nTape2, nTape3 }
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lksk.LKskProof
import at.logic.gapt.proofs.lksk.LKskProof.Label
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.prover9.Prover9
import org.specs2.mutable._

class nTapeTest extends Specification {
  args( skipAll = !Prover9.isInstalled )
  "The higher-order tape proof" should {
    "do cut-elimination on the 2 copies tape proof tape3.llk" in {
      val acnf_labels = nTape2.acnf.conclusion.map( _._1 ).filter( _ != LKskProof.emptyLabel )
      acnf_labels must_== Sequent[Label]()

      val acnf_lkconclusion = nTape2.acnf.conclusion.map( _._2 ) //discard labels
      //println( nTape2.preprocessed_input_proof.conclusion )
      //println( acnf_lkconclusion )
      acnf_lkconclusion.multiSetEquals( nTape2.preprocessed_input_proof.conclusion ) must beTrue

      ok( "acnf could be created" )
    }

    "print statistics of the 2 copies tape proof, including reproving the deep formula (tape3.llk)" in {
      if ( !EProver.isInstalled ) skipped( "No EProver installed!" )
      nTape2.printStatistics()
      ok( "all statistics created!" )
    }

    "do cut-elimination on the 1 copy tape proof tape3ex.llk" in {
      val acnf_labels = nTape3.acnf.conclusion.map( _._1 ).filter( _ != LKskProof.emptyLabel )
      acnf_labels must_== Sequent[Label]()

      val acnf_lkconclusion = nTape3.acnf.conclusion.map( _._2 )
      acnf_lkconclusion.multiSetEquals( nTape3.preprocessed_input_proof.conclusion ) must beTrue

      ok( "acnf could be created" )
    }

    "print statistics of the 3 copies tape proof, including reproving the deep formula tape3ex.llk" in {
      if ( !EProver.isInstalled ) skipped( "No EProver installed!" )
      nTape3.printStatistics()
      ok( "all statistics created!" )
    }
  }

}
