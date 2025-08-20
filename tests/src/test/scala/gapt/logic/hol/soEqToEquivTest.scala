package gapt.logic.hol

import gapt.expr.{Abs, stringInterpolationForExpressions}
import gapt.proofs.ProofBuilder
import gapt.proofs.lk.LKProofMatchers
import gapt.proofs.lk.rules.{EqualityLeftRule, EqualityRightRule, LogicalAxiom, WeakeningLeftRule, WeakeningRightRule}
import org.specs2.mutable.Specification

class soEqToEquivTest extends Specification with LKProofMatchers {
  "soEq2Iff" should {
    "soEq2Iff" in {
      soEqToEquiv.soEq2Iff(hof"(^x ((F : i>o) x)) = (^x ((G : i>o) x))") must beEqualTo(fof"!x (F(x) <-> G(x))")
      soEqToEquiv.soEq2Iff(hof"(F : i>o) x") must beEqualTo(hof"(F : i>o) x")
      soEqToEquiv.soEq2Iff(hof"(A: o) = (B:o)") must beEqualTo(hof"A <-> B")
      soEqToEquiv.soEq2Iff(hof"(x:i) = (y:i)") must beEqualTo(hof"x = y")
      soEqToEquiv.soEq2Iff(hof"C & ((A: o) = (B:o))") must beEqualTo(hof"C & (A <-> B)")
      soEqToEquiv.soEq2Iff(hof"!x (C & ((A: o) = (B:o)))") must beEqualTo(hof"!x (C & (A <-> B))")
    }
    "test 1" in {
      val p = ProofBuilder
        .c(LogicalAxiom(hof"(^x ((F : i>o) x)) = (^x ((G : i>o) x))"))
        .u(p => WeakeningLeftRule(p, fof"A & F(t)"))
        .u(p => EqualityLeftRule(p, hof"(^x ((F : i>o) x)) = (^x ((G : i>o) x))", fof"A & F(t)", Abs(hov"Y : i>o", hof"A & (Y t)")))
        .qed
      val p_ = soEqToEquiv(p)
      p_ must beSkolemFree
      p_ must beProofOf(p.endSequent.map {
        soEqToEquiv.soEq2Iff
      })
    }
    "test 2" in {
      val e = hof"(^x ^y ((F : i>i>o) x y)) = (^x ^y ((G : i>i>o) x y))"
      val p = ProofBuilder
        .c(LogicalAxiom(e))
        .u(p => WeakeningRightRule(p, fof"!x !y (F(x,y) -> A)"))
        .u(p => EqualityRightRule(p, e, fof"!x !y (F(x,y) -> A)", Abs(hov"Y : i>i>o", hof"!x !y ((Y x y) -> A)")))
        .qed
      val p_ = soEqToEquiv(p)
      p_ must beSkolemFree
      p_ must beProofOf(p.endSequent.map {
        soEqToEquiv.soEq2Iff
      })
    }
  }
}
