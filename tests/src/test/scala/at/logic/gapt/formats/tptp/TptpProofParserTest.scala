package at.logic.gapt.formats.tptp

import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.proofs.Clause
import at.logic.gapt.proofs.resolution.{ ResolutionToExpansionProof, ResolutionToLKProof, fixDerivation }
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable._
import org.specs2.specification.core.Fragments

import scalaz._

class TptpProofParserTest extends Specification {

  Fragments.foreach( Seq(
    "RNG103+2_E---1.9.THM-CRf.s",
    "ALG011-1_Metis---2.3.UNS-CRf.s",
    "GEO008-3_iprover-1.4.tptp",
    "LCL101-1_Vampire---4.0.UNS-REF.s",
    "SYN728-1_VampireZ3---1.0.UNS-Ref.s",
    "HEN005-6_SPASS-3.7.UNS-Ref.s",
    "counting-cnf.vampire.tptp"
  ) ) { fn =>
    fn in {
      val ( endSequent, sketch ) = TptpProofParser.parse( ClasspathInputFile( fn ) )
      sketch.conclusion must_== Clause()

      val Success( robinson ) = RefutationSketchToResolution( sketch )
      robinson.conclusion must_== Clause()

      val fixed = fixDerivation( robinson, endSequent )

      // not converting that one to LK because it takes too long
      if ( fn != "RNG103+2_E---1.9.THM-CRf.s" )
        ResolutionToLKProof( fixed )

      val expansion = ResolutionToExpansionProof( fixed )
      Escargot isValid expansion.deep must_== true
    }
  }
}
