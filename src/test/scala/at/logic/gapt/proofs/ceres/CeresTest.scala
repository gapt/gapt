package at.logic.gapt.proofs.ceres

import at.logic.gapt.formats.llkNew._
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkNew.LKProof
import at.logic.gapt.utils.testing.ClasspathFileCopier
import org.specs2.mutable._

import scala.collection.Set

/**
 * Created by marty on 11/24/15.
 */
class CeresTest extends Specification with ClasspathFileCopier {
  def load( file: String, pname: String ) = {
    val filename = tempCopyOfClasspathFile( file )
    loadLLK( filename ).eproofs.find( _._1.toString == pname ) match {
      case None             => throw new Exception( "could not find the proof in proof db!" )
      case Some( ( _, p ) ) => p
    }
  }

  "Struct extraction" should {
    "work for the permutation proof" in {
      skipped( "" )
      val proof = load( "perm.llk", "TheProof" )
      val acnf = CERES( proof )
      ( acnf.endSequent multiSetEquals proof.endSequent ) must beTrue
      ok( "everything done" )
    }

    "work for simple equations (1)" in {
      skipped( "" )
      val proof = load( "eqsimple.llk", "Proof1" )
      val acnf = CERES( proof )
      ( acnf.endSequent multiSetEquals proof.endSequent ) must beTrue
      ok( "everything done" )
    }
    "work for simple equations (2)" in {
      skipped( "" )
      val proof = load( "eqsimple.llk", "Proof2" )
      val acnf = CERES( proof )
      ( acnf.endSequent multiSetEquals proof.endSequent ) must beTrue
      ok( "everything done" )
    }
    "work for simple equations (3)" in {
      val proof = load( "eqsimple.llk", "Proof3" )
      val acnf = CERES( proof )
      ( acnf.endSequent multiSetEquals proof.endSequent ) must beTrue
      ok( "everything done" )
    }
  }

}
