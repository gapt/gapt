package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.primediv
import at.logic.gapt.proofs.SequentMatchers
import org.specs2.mutable.Specification

class SkolemizeInferencesTest extends Specification with SequentMatchers {

  "primediv" in {
    val p = DefinitionElimination( primediv.defs )( primediv.proof )
    val sk = skolemizeInferences( p )
    sk.endSequent must beMultiSetEqual( p.endSequent )
  }

}
