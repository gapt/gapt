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
  "Struct extraction" should {
    "work for the permutation proof" in {
      val filename = tempCopyOfClasspathFile( "perm.llk" )
      //workaround until .proof returns a new LKProof again (after the xml conversion)
      val proof: LKProof = loadLLK( filename ).eproofs.find( _._1.toString == "TheProof" ) match {
        case None             => throw new Exception( "could not find the proof in proof db!" )
        case Some( ( _, p ) ) => p
      }
      val acnf = CERES( proof )
      ( acnf.endSequent multiSetEquals proof.endSequent ) must beTrue
      ok( "everything done" )
    }
  }

}
