package at.logic.gapt.expr.fol

import at.logic.gapt.expr.FOLAtom
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class ThresholdsTest extends Specification with SatMatchers {
  "atMost.oneOf iff exactly.oneOf or noneOf" in {
    val atoms = ( 0 to 7 ) map { i => FOLAtom( i toString ) }
    ( thresholds.atMost oneOf atoms ) <-> ( ( thresholds.exactly oneOf atoms ) | ( thresholds.exactly noneOf atoms ) ) must beValid
  }

  "all are sat" in {
    val atoms = ( 0 to 7 ) map { i => FOLAtom( i toString ) }
    ( thresholds.atMost oneOf atoms ) must beSat
    ( thresholds.exactly oneOf atoms ) must beSat
    ( thresholds.exactly noneOf atoms ) must beSat
  }
}
