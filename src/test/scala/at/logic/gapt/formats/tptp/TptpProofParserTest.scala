package at.logic.gapt.formats.tptp

import at.logic.gapt.proofs.Clause
import at.logic.gapt.proofs.expansionTrees.toDeep
import at.logic.gapt.proofs.resolution.{ RobinsonToLK, RobinsonToExpansionProof }
import at.logic.gapt.proofs.sketch.RefutationSketchToRobinson
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.veriT.VeriTProver
import org.specs2.mutable._

import scala.io.Source

class TptpProofParserTest extends Specification {

  def load( fn: String ): String = Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( fn ) ).mkString

  val p9 = new Prover9Prover
  val veriT = new VeriTProver

  "RNG103p2 from eprover" in {
    val ( endSequent, sketch ) = TptpProofParser.parse( load( "RNG103+2_E---1.9.THM-CRf.s" ) )
    sketch.conclusion must_== Clause()

    if ( !p9.isInstalled || !veriT.isInstalled ) skipped
    val Some( robinson ) = RefutationSketchToRobinson( sketch, p9 )
    robinson.conclusion must_== Clause()
    val expansion = RobinsonToExpansionProof( robinson, endSequent )
    veriT.isValid( toDeep( expansion ) ) must_== true
  }

  "ALG011m1 from metis" in {
    val ( endSequent, sketch ) = TptpProofParser.parse( load( "ALG011-1_Metis---2.3.UNS-CRf.s" ) )
    sketch.conclusion must_== Clause()

    if ( !p9.isInstalled || !veriT.isInstalled ) skipped
    val Some( robinson ) = RefutationSketchToRobinson( sketch, p9 )
    robinson.conclusion must_== Clause()
    RobinsonToExpansionProof( robinson, endSequent )
    val expansion = RobinsonToExpansionProof( robinson, endSequent )
    veriT.isValid( toDeep( expansion ) ) must_== true
    RobinsonToLK( robinson, endSequent )
    ok
  }

  "GEO008m3 from iprover" in {
    val ( endSequent, sketch ) = TptpProofParser.parse( load( "GEO008-3_iprover-1.4.tptp" ) )
    sketch.conclusion must_== Clause()

    if ( !p9.isInstalled || !veriT.isInstalled ) skipped
    val Some( robinson ) = RefutationSketchToRobinson( sketch, p9 )
    robinson.conclusion must_== Clause()
    RobinsonToExpansionProof( robinson, endSequent )
    val expansion = RobinsonToExpansionProof( robinson, endSequent )
    veriT.isValid( toDeep( expansion ) ) must_== true
    RobinsonToLK( robinson, endSequent )
    ok
  }

  "LCL101m1 from vampire" in {
    val ( endSequent, sketch ) = TptpProofParser.parse( load( "LCL101-1_Vampire---4.0.UNS-REF.s" ) )
    sketch.conclusion must_== Clause()

    if ( !p9.isInstalled || !veriT.isInstalled ) skipped
    val Some( robinson ) = RefutationSketchToRobinson( sketch, p9 )
    robinson.conclusion must_== Clause()
    RobinsonToExpansionProof( robinson, endSequent )
    val expansion = RobinsonToExpansionProof( robinson, endSequent )
    veriT.isValid( toDeep( expansion ) ) must_== true
    RobinsonToLK( robinson, endSequent )
    ok
  }

  "HEN005m1 from spass" in {
    val ( endSequent, sketch ) = TptpProofParser.parse( load( "HEN005-6_SPASS-3.7.UNS-Ref.s" ) )
    sketch.conclusion must_== Clause()

    if ( !p9.isInstalled || !veriT.isInstalled ) skipped
    val Some( robinson ) = RefutationSketchToRobinson( sketch, p9 )
    robinson.conclusion must_== Clause()
    RobinsonToExpansionProof( robinson, endSequent )
    val expansion = RobinsonToExpansionProof( robinson, endSequent )
    veriT.isValid( toDeep( expansion ) ) must_== true
    RobinsonToLK( robinson, endSequent )
    ok
  }

}
