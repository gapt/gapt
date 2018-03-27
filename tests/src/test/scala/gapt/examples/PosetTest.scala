package gapt.examples

import org.specs2.mutable.Specification

class PosetTest extends Specification {
  "proof" in {
    import poset.proof._
    ctx.check( cycleImpliesEqual3 )
    ctx.check( cycleImpliesEqual4 )
    ok
  }
}
