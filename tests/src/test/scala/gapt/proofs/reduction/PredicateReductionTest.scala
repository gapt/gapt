package gapt.proofs.reduction

import gapt.expr._
import gapt.proofs.SequentMatchers
import org.specs2.mutable._

class PredicateReductionTest extends Specification with SequentMatchers {
  "predicate reduction should" in {
    "add non-emptiness axioms to antecedent" in {
      val ( f, _ ) = PredicateReductionET forward hos":- P(x : i)"
      f.antecedent must contain( allOf( hof"?x is_i(x)" ) )
    }
    "guard universal quantification" in {
      val ( f, _ ) = PredicateReductionET forward hos":- !x P(x:a)"
      f.succedent must contain( exactly( hof"!x ( is_a(x) -> P(x:a) )" ) )
    }
    "guard existential quantification" in {
      val ( f, _ ) = PredicateReductionET forward hos":- ?x P(x:a)"
      f.succedent must contain( exactly( hof"?x ( is_a(x) & P(x:a) )" ) )
    }
    "introduce axioms for function symbols" in {
      val ( f, _ ) = PredicateReductionET forward hos":- P(f(x))"
      f.antecedent must contain( allOf( hof"!x (is_i(x) -> is_i(f(x)))" ) )
    }
  }
}
