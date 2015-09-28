package at.logic.gapt.formats.tptp

import at.logic.gapt.proofs.Clause
import at.logic.gapt.proofs.expansionTrees.toDeep
import at.logic.gapt.proofs.resolution.{ RobinsonToLK, RobinsonToExpansionProof }
import at.logic.gapt.proofs.sketch.RefutationSketchToRobinson
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.veriT.VeriTProver
import org.specs2.mutable._
import org.specs2.specification.core.Fragments

import scala.io.Source

class TptpProofParserTest extends Specification {

  def load( fn: String ): String = Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( fn ) ).mkString

  val p9 = new Prover9Prover
  val veriT = new VeriTProver

  Fragments.foreach( Seq(
    "RNG103+2_E---1.9.THM-CRf.s",
    "ALG011-1_Metis---2.3.UNS-CRf.s",
    "GEO008-3_iprover-1.4.tptp",
    "LCL101-1_Vampire---4.0.UNS-REF.s",
    "HEN005-6_SPASS-3.7.UNS-Ref.s"
  ) ) { fn =>
    fn in {
      val ( endSequent, sketch ) = TptpProofParser.parse( load( fn ) )
      sketch.conclusion must_== Clause()

      if ( !p9.isInstalled || !veriT.isInstalled ) skipped

      val Some( robinson ) = RefutationSketchToRobinson( sketch, p9 )
      robinson.conclusion must_== Clause()

      // not converting that one to LK because it takes too long
      if ( fn != "RNG103+2_E---1.9.THM-CRf.s" )
        RobinsonToLK( robinson, endSequent )

      val expansion = RobinsonToExpansionProof( robinson, endSequent )
      veriT.isValid( toDeep( expansion ) ) must_== true
    }
  }
}
