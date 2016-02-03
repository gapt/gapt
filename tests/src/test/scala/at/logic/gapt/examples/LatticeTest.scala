package at.logic.gapt.examples

import at.logic.gapt.proofs.lk.DefinitionElimination
import org.specs2.mutable.Specification

class LatticeTest extends Specification {
  "lattice" in { lattice; ok }
  "definition elimination" in { DefinitionElimination( lattice.defs )( lattice.p ); ok }
}
