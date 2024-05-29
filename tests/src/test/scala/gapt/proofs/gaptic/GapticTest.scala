package gapt.proofs.gaptic

import gapt.proofs.Sequent
import gapt.expr._
import gapt.proofs.gaptic.tactics.ForwardChain
import org.specs2.mutable.Specification

class GapticTest extends Specification {

  "rewrite simple" in {
    Proof(
      ("ass" -> hof"P(f(a))") +:
        ("eq" -> hof"!x f(x) = g(x)") +:
        Sequent()
        :+ ("goal" -> hof"P(g(a))")
    ) {
      rewrite rtl "eq" in "goal"
      prop
    }
    ok
  }
  "rewrite addition" in {
    Proof(
      ("add0" -> hof"!x x+0 = x") +:
        ("adds" -> hof"!x!y x+s(y) = s(x+y)") +:
        Sequent()
        :+ ("goal" -> hof"s(s(0)) + s(s(0)) = s(s(s(s(0))))")
    ) {
      rewrite.many.ltr("add0", "adds") in "goal"
      axiomRefl
    }
    ok
  }

  "forward chaining" in {

    "should fail if lemma" in {

      "is not found" in {
        Proof(
          hols"""
            target: q(f(c), g(d)),
            abc:    !x !y (q x y -> p (f x) (g y))
            :-
            goal:   p(f(f(c)), g(g(d)))
            """
        ) {
          ForwardChain("lemma", OnLabel("target"))
        } must throwA[TacticFailureException]
      }

      "is in succedent" in {
        Proof(
          hols"""
            target: q(f(c), g(d))
            :-
            lemma:  !x !y (q x y -> p (f x) (g y)),
            goal:   p(f(f(c)), g(g(d)))
            """
        ) {
          ForwardChain("lemma", OnLabel("target"))
        } must throwA[TacticFailureException]
      }

      "is not of the form !x (P(x) -> Q(x))" in {
        Proof(
          hols"""
            target: q(f(c), g(d)),
            lemma:  !x !y (q x y & p (f x) (g y))
            :-
            goal:   p(f(f(c)), g(g(d)))
            """
        ) {
          ForwardChain("lemma", OnLabel("target"))
        } must throwA[TacticFailureException]
      }
    }

    "should fail if target" in {
      "cannot be found" in {
        Proof(
          hols"""
            lemma: !x !y (q x y -> p (f x) (g y))
            :-
            goal:  p(f(f(c)), g(g(d)))
            """
        ) {
          ForwardChain("lemma")
        } must throwA[TacticFailureException]
      }

      "is in succedent" in {
        Proof(
          hols"""
            lemma:  !x !y (q x y -> p (f x) (g y))
            :-
            target: q(f(c), g(d)),
            goal:   p(f(f(c)), g(g(d)))
            """
        ) {
          ForwardChain("lemma")
        } must throwA[TacticFailureException]
      }

      "label does not exist" in {
        Proof(
          hols"""
            abc:   q(f(c), g(d)),
            lemma: !x !y (q x y -> p (f x) (g y))
            :-
            goal:  p(f(f(c)), g(g(d)))
            """
        ) {
          ForwardChain("lemma", OnLabel("target"))
        } must throwA[TacticFailureException]
      }
    }

    "should succeed" in {
      Proof(
        hols"""
            target: q(f(c), g(d)),
            lemma:  !x !y (q x y -> p (f x) (g y))
            :-
            goal:   p(f(f(c)), g(g(d)))
            """
      ) {
        ForwardChain("lemma", OnLabel("target"))
        trivial
      }
      ok
    }
  }

}
