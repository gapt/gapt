package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.examples.induction.{ numbers, lists }
import at.logic.gapt.proofs.SequentMatchers
import org.specs2.mutable.Specification

class MakeInductionExplicitTest extends Specification with SequentMatchers {

  "numeral induction" in {
    import numbers._
    val explicit = makeInductionExplicit( pluscomm )
    explicit.subProofs.filter { _.isInstanceOf[InductionRule] } must_== Set()
    ctx.check( explicit )
    explicit.conclusion must beMultiSetEqual(
      hof"∀X (X(0) ∧ ∀x (X(x) ⊃ X(s(x))) ⊃ ∀x X(x))" +:
        pluscomm.conclusion
    )
  }

  "list induction" in {
    import lists._
    val explicit = makeInductionExplicit( mapfusion )
    explicit.subProofs.filter { _.isInstanceOf[InductionRule] } must_== Set()
    ctx.check( explicit )
    explicit.conclusion must beMultiSetEqual(
      hof"∀X (X(nil) ∧ ∀x ∀xs (X(xs) ⊃ X(cons(x, xs))) ⊃ ∀x X(x)) " +:
        mapfusion.conclusion
    )
  }

}
