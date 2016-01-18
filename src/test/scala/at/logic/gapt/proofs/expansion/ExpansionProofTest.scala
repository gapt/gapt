package at.logic.gapt.proofs.expansion

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.examples.{ Pi2Pigeonhole, LinearExampleProof }
import at.logic.gapt.proofs.lk.{ solve, LKToExpansionProof }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class ExpansionProofTest extends Specification with SatMatchers {

  "linear example cut intro" in {
    val Some( p ) = CutIntroduction.compressLKProof( LinearExampleProof( 6 ) )
    val e = LKToExpansionProof( p )
    e.deep must beValidSequent
    eliminateCutsET( e ).deep must beValidSequent
  }

  "pi2 pigeonhole" in {
    val e = LKToExpansionProof( Pi2Pigeonhole() )
    Escargot isValid e.deep must_== true
    Escargot isValid eliminateCutsET( e ).deep must_== true
  }

}
