package gapt.proofs.nd

import gapt.examples.Script
import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs._
import org.specs2.mutable._

class transformationTest extends Specification {

  "kolmogorov" in {
    "logicalAxiom1" in {
      val p = LogicalAxiom(hof"A")
      kolmogorov(p).conclusion mustEqual Seq(hof"¬ ¬A") ++: Sequent() :+ hof"¬ ¬A"
    }

    "logicalAxiom2" in {
      val p = LogicalAxiom(hof"A & (B | C)")
      kolmogorov(p).conclusion mustEqual Seq(hof"¬ ¬(¬ ¬A ∧ ¬ ¬(¬ ¬B ∨ ¬ ¬C))") ++: Sequent() :+ hof"¬ ¬(¬ ¬A ∧ ¬ ¬(¬ ¬B ∨ ¬ ¬C))"
    }

    "weakeningRule" in {
      val p1 = LogicalAxiom(hof"A")
      val p2 = WeakeningRule(p1, hof"B")
      kolmogorov(p2).conclusion mustEqual Seq(hof"¬ ¬B", hof"¬ ¬A") ++: Sequent() :+ hof"¬ ¬A"
    }

    "contractionRule" in {
      val p1 = LogicalAxiom(hof"A")
      val p2 = WeakeningRule(p1, hof"A")
      val p3 = ContractionRule(p2, hof"A")
      kolmogorov(p3).conclusion mustEqual Seq(hof"¬ ¬A") ++: Sequent() :+ hof"¬ ¬A"
    }

    "andElim1Rule" in {
      val p1 = LogicalAxiom(hof"A & B")
      val p2 = AndElim1Rule(p1)
      kolmogorov(p2).conclusion mustEqual Seq(hof"¬ ¬(¬ ¬A ∧ ¬ ¬B)") ++: Sequent() :+ hof"¬ ¬A"
    }

    "andElim2Rule" in {
      val p1 = LogicalAxiom(hof"A & B")
      val p2 = AndElim2Rule(p1)
      kolmogorov(p2).conclusion mustEqual Seq(hof"¬ ¬(¬ ¬A ∧ ¬ ¬B)") ++: Sequent() :+ hof"¬ ¬B"
    }

    "andIntroRule" in {
      val p1 = LogicalAxiom(hof"A")
      val p2 = LogicalAxiom(hof"B")
      val p3 = AndIntroRule(p1, p2)
      kolmogorov(p3).conclusion mustEqual Seq(hof"¬ ¬A", hof"¬ ¬B") ++: Sequent() :+ hof"¬ ¬(¬ ¬A ∧ ¬ ¬B)"
    }

    "impElimRule" in {
      val p1 = LogicalAxiom(hof"A -> B")
      val p2 = LogicalAxiom(hof"A")
      val p3 = ImpElimRule(p1, p2)
      kolmogorov(p3).conclusion mustEqual Seq(hof"¬ ¬(¬ ¬A → ¬ ¬B)", hof"¬ ¬A") ++: Sequent() :+ hof"¬ ¬B"
    }

    "impIntroRule" in {
      val p1 = LogicalAxiom(hof"A")
      val p2 = WeakeningRule(p1, hof"B")
      val p3 = ImpIntroRule(p2, hof"B")
      kolmogorov(p3).conclusion mustEqual Seq(hof"¬ ¬A") ++: Sequent() :+ hof"¬ ¬(¬ ¬B → ¬ ¬A)"
    }

    "orElimRule" in {
      val p1 = LogicalAxiom(hof"A | B")

      val p2 = LogicalAxiom(hof"A -> C")
      val p3 = LogicalAxiom(hof"A")
      val p4 = ImpElimRule(p2, p3)

      val p5 = LogicalAxiom(hof"B -> C")
      val p6 = LogicalAxiom(hof"B")
      val p7 = ImpElimRule(p5, p6)

      val p8 = OrElimRule(p1, p4, p7)
      kolmogorov(p8).conclusion mustEqual Seq(hof"¬ ¬(¬ ¬A ∨ ¬ ¬B)", hof"¬ ¬(¬ ¬A → ¬ ¬C)", hof"¬ ¬(¬ ¬B → ¬ ¬C)") ++: Sequent() :+ hof"¬ ¬C"
    }

    "orIntro1Rule" in {
      val p1 = LogicalAxiom(hof"A")
      val p2 = OrIntro1Rule(p1, hof"B")
      kolmogorov(p2).conclusion mustEqual Seq(hof"¬ ¬A") ++: Sequent() :+ hof"¬ ¬(¬ ¬A ∨ ¬ ¬B)"
    }

    "orIntro2Rule" in {
      val p1 = LogicalAxiom(hof"A")
      val p2 = OrIntro2Rule(p1, hof"B")
      kolmogorov(p2).conclusion mustEqual Seq(hof"¬ ¬A") ++: Sequent() :+ hof"¬ ¬(¬ ¬B ∨ ¬ ¬A)"
    }

    "negElimRule" in {
      val p1 = LogicalAxiom(hof"¬A")
      val p2 = LogicalAxiom(hof"A")
      val p3 = NegElimRule(p1, p2)
      kolmogorov(p3).conclusion mustEqual Seq(hof"¬ ¬ ¬A", hof"¬ ¬A") ++: Sequent() :+ hof"¬ ¬ ⊥"
    }

    "negIntroRule" in {
      val p1 = LogicalAxiom(hof"¬A")
      val p2 = LogicalAxiom(hof"A")
      val p3 = NegElimRule(p1, p2)
      val p4 = NegIntroRule(p3, hof"¬A")
      kolmogorov(p4).conclusion mustEqual Seq(hof"¬ ¬A") ++: Sequent() :+ hof"¬ ¬ ¬ ¬A"
    }

    "botElimRule" in {
      val p1 = LogicalAxiom(hof"¬A")
      val p2 = LogicalAxiom(hof"A")
      val p3 = NegElimRule(p1, p2)
      val p4 = BottomElimRule(p3, hof"B")
      kolmogorov(p4).conclusion mustEqual Seq(hof"¬ ¬ ¬A", hof"¬ ¬A") ++: Sequent() :+ hof"¬ ¬B"
    }

    "topIntro" in {
      val p1 = TopIntroRule
      kolmogorov(p1).conclusion mustEqual Seq() ++: Sequent() :+ hof"¬ ¬ ⊤"
    }

    "forallElimRule" in {
      val p1 = LogicalAxiom(hof"!x P(x)")
      val p2 = ForallElimRule(p1, hov"y")
      kolmogorov(p2).conclusion mustEqual Seq(hof"¬ ¬ ∀x ¬ ¬P(x)") ++: Sequent() :+ hof" ¬ ¬P(y)"
    }

    "forallIntroRule" in {
      val p1 = LogicalAxiom(hof"!x P(x)")
      val p2 = ForallElimRule(p1, hov"y")
      val p3 = ForallIntroRule(p2, hov"y", hov"z")
      kolmogorov(p3).conclusion mustEqual Seq(hof"¬ ¬ ∀x ¬ ¬P(x)") ++: Sequent() :+ hof"¬ ¬ ∀z ¬ ¬P(z)"
    }

    "existsElimRule" in {
      val p1 = LogicalAxiom(hof"?x P(x)")
      val p2 = LogicalAxiom(hof"!y (P(y) -> Q)")
      val p3 = ForallElimRule(p2, hov"z")
      val p4 = LogicalAxiom(hof"P(z)")
      val p5 = ImpElimRule(p3, p4)
      val p6 = ExistsElimRule(p1, p5, hov"z")
      kolmogorov(p6).conclusion mustEqual Seq(hof"¬ ¬ ∃x ¬ ¬P(x)", hof"¬ ¬ ∀y ¬ ¬(¬ ¬P(y) → ¬ ¬Q)") ++: Sequent() :+ hof"¬ ¬Q"
    }

    "existsIntroRule" in {
      val p1 = LogicalAxiom(hof"P(x)")
      val p2 = ExistsIntroRule(p1, hof"?x P(x)")
      kolmogorov(p2).conclusion mustEqual Seq(hof"¬ ¬P(x)") ++: Sequent() :+ hof"¬ ¬ ∃x ¬ ¬P(x)"
    }

    "equalityElimRule" in {
      val p1 = LogicalAxiom(hof"s = t")
      val p2 = LogicalAxiom(hof"P(s)")
      val p3 = EqualityElimRule(p1, p2)
      kolmogorov(p3).conclusion mustEqual Seq(hof"¬s != t", hof"¬ ¬P(s)") ++: Sequent() :+ hof"¬ ¬P(t)"
    }

    "equalityIntroRule" in {
      val p1 = EqualityIntroRule(hov"x")
      kolmogorov(p1).conclusion mustEqual Seq() ++: Sequent() :+ hof"¬x != x"
    }

    "inductionRule" in {
      val b1 = LogicalAxiom(hof"!(x: nat) (((x + (0: nat)): nat) = x)")
      val b2 = ForallElimRule(b1, le"0: nat")

      val s1 = LogicalAxiom(hof"!(x: nat) !(y: nat) (((s(x): nat) + y: nat) = s(x + y))")
      val s2 = ForallElimRule(s1, le"x0: nat")
      val s3 = ForallElimRule(s2, le"0: nat")
      val s4 = LogicalAxiom(hof"(((x0: nat) + (0: nat)): nat) = x0")
      val s5 = EqualityElimRule(s4, s3, hof"((((s(x0): nat) + (0: nat)): nat) = s(z: nat))", hov"z: nat")

      val cases = List(
        InductionCase(b2, hoc"0: nat", List.empty, List.empty),
        InductionCase(s5, hoc"s: nat>nat", List(Ant(0)), List(hov"x0: nat"))
      )

      val p = InductionRule(cases, Abs(Var("x", TBase("nat")), hof"(((x: nat) + (0:nat)): nat) = x"), le"x: nat")

      kolmogorov(p).conclusion mustEqual
        Seq(
          hof"¬ ¬ ∀(x:nat) ¬(x:nat) + (0:nat) != (x:nat)",
          hof"¬ ¬ ∀(x:nat) ¬ ¬ ∀(y:nat) ¬s(x:nat) + (y:nat) != s((x:nat) + (y:nat))"
        ) ++:
        Sequent() :+ hof"¬ (x:nat) + (0:nat) != (x:nat)"
    }

    "theoryAxiom" in {
      val p = TheoryAxiom(hof"!x x = x")
      kolmogorov(p).conclusion mustEqual Seq() ++: Sequent() :+ hof"¬ ¬ ∀x ¬x != x"
    }

    "excludedMiddleRule" in {
      val p1 = LogicalAxiom(hof"P")
      val p2 = LogicalAxiom(hof"¬P")
      val p3 = OrIntro1Rule(p1, hof"¬P")
      val p4 = OrIntro2Rule(p2, hof"P")
      val p5 = ExcludedMiddleRule(p3, Ant(0), p4, Ant(0))

      kolmogorov(p5).conclusion mustEqual Seq() ++: Sequent() :+ hof"¬ ¬(¬ ¬P ∨ ¬ ¬ ¬P)"
    }

  }

}
