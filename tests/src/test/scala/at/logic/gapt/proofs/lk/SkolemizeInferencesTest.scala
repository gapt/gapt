package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.{ nTape3, primediv }
import at.logic.gapt.proofs.SequentMatchers
import org.specs2.mutable.Specification

class SkolemizeInferencesTest extends Specification with SequentMatchers {

  "primediv" in {
    val p = primediv.proof
    skolemizeInferences( p ).endSequent must beMultiSetEqual( p.endSequent )
    skolemizeInferences( p, proofTheoretic = false ).endSequent must beMultiSetEqual( p.endSequent )
  }

  "ntape3" in {
    val p = nTape3.input_proof
    skolemizeInferences( p ).endSequent must beMultiSetEqual( p.endSequent )
    skolemizeInferences( p, proofTheoretic = false ).endSequent must beMultiSetEqual( p.endSequent )
  }

}
