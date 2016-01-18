package at.logic.gapt.proofs.ceres

import at.logic.gapt.formats.llkNew._
import at.logic.gapt.proofs.SequentMatchers
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9.Prover9
import org.specs2.mutable._

import scala.io.Source

/**
 * Created by marty on 11/24/15.
 */
class CeresTest extends Specification with SequentMatchers {
  def checkForProverOrSkip = Prover9.isInstalled must beTrue.orSkip

  def load( file: String, pname: String ) =
    LLKProofParser.parseString( Source fromInputStream getClass.getClassLoader.getResourceAsStream( file ) mkString ).proof( pname )

  "Struct extraction" should {
    "work for the permutation proof" in {
      val proof = load( "perm.llk", "TheProof" )
      val acnf = CERES( proof, Escargot )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
    }

    "work for simple equations (1)" in {
      val proof = load( "eqsimple.llk", "Proof1" )
      val acnf = CERES( proof, Escargot )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
    }
    "work for simple equations (2)" in {
      val proof = load( "eqsimple.llk", "Proof2" )
      val acnf = CERES( proof, Escargot )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
    }
    "work for simple equations (3)" in {
      skipped( "produces an error" ) //TODO: fix the error!
      checkForProverOrSkip

      val proof = load( "eqsimple.llk", "Proof3" )
      val acnf = CERES( proof )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
    }
  }

}
