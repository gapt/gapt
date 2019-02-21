package gapt.examples

import gapt.proofs.lk.transformations.eliminateDefinitions
import org.specs2.mutable.Specification

class TapeTest extends Specification {
  import tape._

  "tape" in {
    ctx.check( proof )
    ok
  }

  "definition elimination" in {
    eliminateDefinitions( proof )
    ok
  }

}

class TapeUrbanTest extends Specification {
  import tapeUrban._

  "urban tape" in {
    ctx.check( sigma )
    ok
  }

  "definition elimination" in {
    eliminateDefinitions( sigma )
    ok
  }
}
