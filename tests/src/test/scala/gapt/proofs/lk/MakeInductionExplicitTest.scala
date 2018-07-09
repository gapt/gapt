package gapt.proofs.lk

import gapt.expr._
import gapt.proofs.SequentMatchers
import org.specs2.mutable.Specification

class MakeInductionExplicitTest extends Specification with SequentMatchers {

  "numeral induction" in {
    import gapt.examples.theories.nat._
    val explicit = makeInductionExplicit( addcomm.proof )
    explicit.subProofs.filter { _.isInstanceOf[InductionRule] } must_== Set()
    ctx.check( explicit )
    explicit.conclusion must beMultiSetEqual(
      hof"∀X (X(0) ∧ ∀x (X(x) → X(s(x))) → ∀x X(x))" +:
        addcomm.proof.conclusion )
  }

  "list induction" in {
    import gapt.examples.theories.list._
    val explicit = makeInductionExplicit( mapmap.proof )
    explicit.subProofs.filter { _.isInstanceOf[InductionRule] } must_== Set()
    ( ctx + Ti ).check( explicit )
    explicit.conclusion must beMultiSetEqual(
      hof"∀X (X(nil) ∧ ∀x ∀xs (X(xs) → X(cons(x:?a_1, xs))) → ∀x X(x)) " +:
        mapmap.proof.conclusion )
  }

}
