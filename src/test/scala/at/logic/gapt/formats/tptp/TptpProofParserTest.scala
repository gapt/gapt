package at.logic.gapt.formats.tptp

import at.logic.gapt.proofs.Clause
import at.logic.gapt.proofs.resolution.{ RobinsonToLK, RobinsonToExpansionProof }
import at.logic.gapt.proofs.sketch.RefutationSketchToRobinson
import at.logic.gapt.provers.prover9.Prover9Prover
import org.specs2.mutable._

import scala.io.Source

class TptpProofParserTest extends Specification {

  def load( fn: String ): String = Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( fn ) ).mkString

  val p9 = new Prover9Prover

  "RNG103p2" in {
    "parse as refutation sketch" in {
      TptpProofParser.parse( load( "RNG103+2_E---1.9.THM-CRf.s" ) )._2.conclusion must_== Clause()
    }

    "convert to expansion proof" in {
      if ( !p9.isInstalled ) skipped
      val ( endSequent, sketch ) = TptpProofParser.parse( load( "RNG103+2_E---1.9.THM-CRf.s" ) )
      val Some( robinson ) = RefutationSketchToRobinson( sketch, p9 )
      robinson.conclusion must_== Clause()
      RobinsonToExpansionProof( robinson, endSequent )
      ok
    }
  }

}
