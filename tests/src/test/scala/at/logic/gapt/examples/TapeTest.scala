package at.logic.gapt.examples

import at.logic.gapt.proofs.lk.eliminateDefinitions
import org.specs2.mutable.Specification

class TapeTest extends Specification {

  "tape" in {
    tape.ctx.check( tape.p )
    ok
  }

  "definition elimination" in {
    eliminateDefinitions( tape.defs.toMap )( tape.p )
    ok
  }

}

class TapeUrbanTest extends Specification {
  "urban tape" in {
    tapeUrban.ctx.check( tapeUrban.sigma )
    ok
  }

  "definition elimination" in {
    eliminateDefinitions( tapeUrban.defs.toMap )( tapeUrban.sigma )
    ok
  }
}
