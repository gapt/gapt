package at.logic.gapt.examples

import at.logic.gapt.proofs.lk.eliminateDefinitions
import org.specs2.mutable.Specification

class LatticeTest extends Specification {
  "lattice" in {
    lattice.ctx.check( lattice.p )
    ok
  }
  "definition elimination" in { eliminateDefinitions( lattice.defs )( lattice.p ); ok }
}
