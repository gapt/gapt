package gapt.examples

import org.specs2.mutable.Specification

class SimpleTest extends Specification {
  "fol1" in { fol1.ctx.check( fol1.proof ); ok }
}
