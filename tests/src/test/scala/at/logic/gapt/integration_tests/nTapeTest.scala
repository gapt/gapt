package at.logic.gapt.integration_tests

import at.logic.gapt.examples.nTape
import at.logic.gapt.formats.llkNew.loadLLK
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lkskNew.LKskProof
import at.logic.gapt.proofs.lkskNew.LKskProof.Label
import at.logic.gapt.provers.prover9.Prover9

import org.specs2.mutable._

class nTapeTest extends Specification {
  object nTape2Test extends nTape {
    override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream "tape3.llk" )
    override def root_proof() = "TAPEPROOF"
  }

  object nTape3Test extends nTape {
    override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream "tape3ex.llk" )
    override def root_proof() = "TAPEPROOF"
  }

  args( skipAll = !Prover9.isInstalled )
  "The higher-order tape proof" should {
    "do cut-elimination on the 2 copies tape proof (tape3.llk)" in {
      val acnf_labels = nTape2Test.acnf.conclusion.map( _._1 ).filter( _ != LKskProof.emptyLabel )
      acnf_labels must_== Sequent[Label]()

      val acnf_lkconclusion = nTape2Test.acnf.conclusion.map( _._2 ) //discard labels
      println( nTape2Test.preprocessed_input_proof.conclusion )
      println( acnf_lkconclusion )
      acnf_lkconclusion.multiSetEquals( nTape2Test.preprocessed_input_proof.conclusion ) must beTrue

      ok( "acnf could be created" )
    }

    "do cut-elimination on the 1 copy tape proof (tape3ex.llk)" in {
      //skipped( "fails because projections add too much end-sequent material" )
      val acnf_labels = nTape3Test.acnf.conclusion.map( _._1 ).filter( _ != LKskProof.emptyLabel )
      acnf_labels must_== Sequent[Label]()

      val acnf_lkconclusion = nTape3Test.acnf.conclusion.map( _._2 )
      acnf_lkconclusion.multiSetEquals( nTape3Test.preprocessed_input_proof.conclusion ) must beTrue

      ok( "acnf could be created" )
    }

  }

}
