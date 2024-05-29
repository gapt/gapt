package gapt.proofs.reduction

import gapt.expr._
import gapt.logic.Polarity
import gapt.proofs.Sequent
import gapt.proofs.SequentMatchers
import gapt.proofs.expansion.ETtAtom
import gapt.proofs.expansion.ETtBinary
import gapt.proofs.expansion.ETtStrong
import gapt.proofs.expansion.ETtWeak
import gapt.proofs.expansion.ExpansionProof
import gapt.proofs.expansion.ExpansionTree
import gapt.proofs.expansion.RichExpansionSequent
import gapt.provers.escargot.Escargot
import org.specs2.mutable._

class PredicateReductionTest extends Specification with SequentMatchers {
  "predicate reduction should" in {
    "add non-emptiness axioms to antecedent" in {
      val (f, _) = PredicateReductionET forward hos":- P(x : i)"
      f.antecedent must contain(allOf(hof"?x is_i(x)"))
    }
    "guard universal quantification" in {
      val (f, _) = PredicateReductionET forward hos":- !x P(x:a)"
      f.succedent must contain(exactly(hof"!x ( is_a(x) -> P(x:a) )"))
    }
    "guard existential quantification" in {
      val (f, _) = PredicateReductionET forward hos":- ?x P(x:a)"
      f.succedent must contain(exactly(hof"?x ( is_a(x) & P(x:a) )"))
    }
    "introduce axioms for function symbols" in {
      val (f, _) = PredicateReductionET forward hos":- P(f(x))"
      f.antecedent must contain(allOf(hof"!x (is_i(x) -> is_i(f(x)))"))
    }
  }
  "predicate backtranslation should" in {
    "unguard universal quantifiers" in {
      val (f, back) = PredicateReductionET forward hos"!x P(x:a) :- P(#c(c:a))"
      f must beMultiSetEqual(hos"⊤ -> is_a(#c(c:a)), ?x is_a(x:a), !x (is_a(x) -> P(x:a)) :- P(c)")
      val p_ = ExpansionProof(
        ExpansionTree(
          hof"⊤ -> is_a(#c(c:a))",
          Polarity.Negative,
          ETtBinary(ETtAtom, ETtAtom)
        ) +:
          ExpansionTree(
            hof"!x (is_a(x:a) -> P(x))",
            Polarity.Negative,
            ETtWeak(hov"x_0 : a" -> ETtBinary(ETtAtom, ETtAtom))
          ) +:
          Sequent[ExpansionTree]() :+
          ExpansionTree(
            hof"P( #c(c:a) )",
            Polarity.Positive,
            ETtAtom
          )
      )
      val p = ExpansionTree(
        hof"!x P(x : a)",
        Polarity.Negative,
        ETtWeak(hov"x_0 : a" -> ETtAtom)
      ) +:
        Sequent[ExpansionTree]() :+
        ExpansionTree(
          hof"P(#c(c:a))",
          Polarity.Positive,
          ETtAtom
        )
      println(p_)
      println(back(p_))
      back(p_).shallow must beMultiSetEqual(p.shallow)
    }
  }
}
