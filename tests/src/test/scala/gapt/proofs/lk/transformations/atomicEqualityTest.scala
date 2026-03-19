package gapt.proofs.lk.transformations

import gapt.expr.{Abs, stringInterpolationForExpressions}
import gapt.proofs.gaptic.OpenAssumption
import gapt.proofs.lk.LKProofMatchers
import gapt.proofs.lk.rules.{EqualityLeftRule, EqualityRightRule}
import gapt.proofs.{ProofBuilder, Sequent}
import org.specs2.mutable.Specification

class atomicEqualityTest extends Specification with LKProofMatchers {
  "" should {
    "equality left: and" in {
      val p = ProofBuilder
        .c(OpenAssumption(("" -> hof"s = t") +: ("" -> hof"A(t) & B(t)") +: Sequent()))
        .u(p => EqualityLeftRule(p, hof"s = t", fof"A(t) & B(t)", Abs(hov"Y : i", hof"A(Y) & B(Y)")))
        .qed.asInstanceOf[EqualityLeftRule]
      val r = atomicEquality(p)
      r must beProofOf(p.endSequent)
      r must beSkolemFree
      r must haveAtomicEqualityOnly
    }
    "equality left: forall" in {
      val p = ProofBuilder
        .c(OpenAssumption(("" -> hof"s = t") +: ("" -> hof"!x (A(x,t) & B(t,x))") +: Sequent()))
        .u(p => EqualityLeftRule(p, hof"s = t", fof"!x (A(x,t) & B(t,x))", Abs(hov"Y : i", hof"!x (A(x,Y) & B(Y,x))")))
        .qed.asInstanceOf[EqualityLeftRule]
      val r = atomicEquality(p)
      r must beProofOf(p.endSequent)
      r must beSkolemFree
      r must haveAtomicEqualityOnly
    }
    "equality right" in {
      val p = ProofBuilder
        .c(OpenAssumption(("" -> hof"s = t") +: Sequent() :+ ("" -> hof"A(t) & B(t)")))
        .u(p => EqualityRightRule(p, hof"s = t", fof"A(t) & B(t)", Abs(hov"Y : i", hof"A(Y) & B(Y)")))
        .qed.asInstanceOf[EqualityRightRule]
      val r = atomicEquality(p)
      r must beProofOf(p.endSequent)
      r must beSkolemFree
      r must haveAtomicEqualityOnly
    }
    "equality right: forall" in {
      val p = ProofBuilder
        .c(OpenAssumption(("" -> hof"s = t") +: Sequent() :+ ("" -> hof"!x (A(x,t) & B(t,x))")))
        .u(p => EqualityRightRule(p, hof"s = t", fof"!x (A(x,t) & B(t,x))", Abs(hov"Y : i", hof"!x (A(x,Y) & B(Y,x))")))
        .qed.asInstanceOf[EqualityRightRule]
      val r = atomicEquality(p)
      r must beProofOf(p.endSequent)
      r must beSkolemFree
      r must haveAtomicEqualityOnly
    }
  }
}
