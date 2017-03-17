package at.logic.gapt.examples

import at.logic.gapt.proofs.lk.eliminateDefinitions
import org.specs2.mutable.Specification

class LatticeTest extends Specification {
  import lattice._
  "lattice" in { ctx.check( proof ); ok }
  "definition elimination" in { eliminateDefinitions( proof ); ok }
}
