package at.logic.gapt.proofs.expansion

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.examples.{ Pi2Pigeonhole, LinearExampleProof }
import at.logic.gapt.proofs.lk.{ solve, LKToExpansionProof }
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class ExpansionProofTest extends Specification with SatMatchers {

  "linear example cut intro" in {
    if ( !Prover9.isInstalled ) skipped
    val Some( p ) = CutIntroduction.compressLKProof( LinearExampleProof( 6 ) )
    val e = LKToExpansionProof( p )
    e.deep must beValidSequent
    eliminateCutsET( e ).deep must beValidSequent
  }

  "pi2 pigeonhole" in {
    if ( !Prover9.isInstalled || !Z3.isInstalled ) skipped
    val e = LKToExpansionProof( Pi2Pigeonhole() )
    Z3 isValid e.deep must_== true
    Z3 isValid eliminateCutsET( e ).deep must_== true
  }

}
