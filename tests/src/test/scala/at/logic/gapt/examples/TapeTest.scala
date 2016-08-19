package at.logic.gapt.examples

import at.logic.gapt.proofs.lk.DefinitionElimination
import org.specs2.mutable.Specification

class TapeTest extends Specification {

  "tape" in {
    tape.ctx.check( tape.p )
    ok
  }

  "definition elimination" in {
    DefinitionElimination( tape.defs.toMap )( tape.p )
    ok
  }

}

class TapeUrbanTest extends Specification {
  "urban tape" in {
    tapeUrban.ctx.check( tapeUrban.sigma )
    ok
  }

  "definition elimination" in {
    DefinitionElimination( tapeUrban.defs.toMap )( tapeUrban.sigma )
    ok
  }
}
