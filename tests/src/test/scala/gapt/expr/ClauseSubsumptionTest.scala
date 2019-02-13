package gapt.expr

import gapt.expr.util.clauseSubsumption
import gapt.proofs.Sequent
import org.specs2.mutable.Specification

class ClauseSubsumptionTest extends Specification {

  "quantifiers" in {
    clauseSubsumption(
      hof"∀x x=x" +: Sequent() :+ hof"x=x",
      hof"∀x x=x" +: Sequent() :+ hof"y=y" ) must beSome
  }

}
