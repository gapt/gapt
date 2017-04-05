package at.logic.gapt.formats.lean

import at.logic.gapt.examples._
import org.specs2.mutable._

class LeanExporterTest extends Specification {
  args( skipAll = !LeanChecker.isInstalled )
  "euclid3" in { LeanChecker( prime.euclid3.ctx, prime.euclid3.proof ) must beRight }
  "furstenberg3" in { LeanChecker( prime.furstenberg3.ctx, prime.furstenberg3.proof ) must beRight }
  "lattice" in { LeanChecker( lattice.ctx, lattice.p ) must beRight }
  "tape" in { LeanChecker( tape.ctx, tape.proof ) must beRight }
  "tapeUrban" in { LeanChecker( tapeUrban.ctx, tapeUrban.proof ) must beRight }
  "primediv" in { LeanChecker( primediv.ctx, primediv.proof ) must beRight }
  "pi2pigeonhole" in { LeanChecker( Pi2Pigeonhole.ctx, Pi2Pigeonhole.proof ) must beRight }
  "pi3pigeonhole" in { LeanChecker( Pi3Pigeonhole.ctx, Pi2Pigeonhole.proof ) must beRight }
}
