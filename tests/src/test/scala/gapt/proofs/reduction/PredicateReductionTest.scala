package gapt.proofs.reduction

import gapt.expr._
import gapt.proofs.SequentMatchers
import org.specs2.mutable._

class PredicateReductionTest extends Specification with SequentMatchers {
  "predicate reduction should" in {
    "work with equality" in {
      val ( f, _ ) = PredicateReductionET forward hos":- #v(x:a) = y"
      f must beMultiSetEqual( hos"is_a(nonempty_a:a) :- #v(x:a) = y" )
    }
    "guard universal quantification" in {
      val ( f, _ ) = PredicateReductionET forward hos":- !x P(x:a)"
      f must beMultiSetEqual( hos"is_a(nonempty_a:a) :- !x ( is_a(x) -> P(x:a) )" )
    }
    "guard existential quantification" in {
      val ( f, _ ) = PredicateReductionET forward hos":- ?x P(x:a)"
      f must beMultiSetEqual( hos"is_a(nonempty_a:a) :- ?x ( is_a(x) & P(x:a) )" )
    }
    "abstract the sort of individuals" in {
      val ( f, _ ) = PredicateReductionET forward hos":- P(x)"
      f must beMultiSetEqual( hos"is_i(nonempty_i:i) :- P(x)" )
    }
    "introduce axioms for function symbols" in {
      val ( f, _ ) = PredicateReductionET forward hos":- P(f(x))"
      f must beMultiSetEqual( hos"!x (is_i(x) -> is_i(f(x))), is_i(nonempty_i:i) :- P(f(x))" )
    }
  }
}
