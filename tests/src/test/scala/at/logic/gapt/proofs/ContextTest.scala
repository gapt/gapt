package at.logic.gapt.proofs

import at.logic.gapt.expr._

import org.specs2.mutable.Specification

class ContextTest extends Specification {
  import Context._

  "inductive type" in {
    "negative occurrences" in {
      default +
        InductiveType(
          "large",
          hoc"emptyset : large",
          hoc"comprehension : (large > o) > large"
        ) must throwAn[IllegalArgumentException]
    }
  }

}
