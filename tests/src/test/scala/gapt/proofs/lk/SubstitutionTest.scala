package gapt.proofs.lk

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Atom
import gapt.expr.formula.fol.FOLAtomConst
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.formula.fol.FOLVar
import gapt.expr.subst.Substitution
import gapt.proofs._
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.InductionCase
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import org.specs2.mutable._

class SubstitutionTest extends Specification with SequentMatchers {
  "Substitutions" should {
    object proof1 {
      val x = FOLVar("x")
      val P = FOLAtomConst("P", 1)
      val a = FOLConst("a")
      val f = FOLFunctionConst("f", 1)

      val ax1 = LogicalAxiom(P(x))
      val ax2 = LogicalAxiom(P(x))
      val proof = CutRule(ax1, Suc(0), ax2, Ant(0))
      val subst = Substitution(x, f(a))
    }

    object proof2 {
      val x = FOLVar("x")
      val y = FOLVar("y")
      val P = FOLAtomConst("P", 2)
      val pxy = Atom(P, List(x, y))
      val allxpx = All(x, P(x, y))
      val ax1 = LogicalAxiom(P(x, y))
      val r1 = ForallLeftRule(ax1, allxpx, x)
      val proof = ForallRightRule(r1, allxpx, x)

      val a = FOLConst("a")
      val f = FOLFunctionConst("f", 1)
      val subst = Substitution(y, f(a))
      val subst2 = Substitution(y, x) // test for overbinding
    }

    "apply correctly to a simple proof" in {
      import proof1._
      val p_s = subst(proof)
      p_s.endSequent must beMultiSetEqual(P(f(a)) +: Sequent() :+ P(f(a)))
    }

    "apply correctly to a proof with quantifiers" in {
      import proof2._
      val p_s = subst(proof)
      val pfa = All(x, P(x, f(a)))
      p_s.endSequent must beMultiSetEqual(pfa +: Sequent() :+ pfa)
    }

    "apply correctly to a proof with quantifiers with overbinding" in {
      import proof2._
      val p_s = subst2(proof)
      val pfa = All(y, P(y, x))
      p_s.endSequent must beMultiSetEqual(pfa +: Sequent() :+ pfa)
    }

  }

  "induction" in {
    var ctx = Context()
    ctx += Sort("sk")
    ctx += InductiveType("list", hoc"nil: list", hoc"cons:sk>list>list")
    ctx += hoc"B:list>o"
    ctx += hoc"t:list"
    val proof = (ProofBuilder
      c LogicalAxiom(hof"B(nil:list)")
      u (WeakeningLeftRule(_, hof"C(x_0:sk, xs_0:list)"))
      c LogicalAxiom(hof"A")
      u (WeakeningLeftRule(_, hof"B(xs_1:list)"))
      u (WeakeningRightRule(_, hof"B(cons(x_1:sk, xs_1:list):list)"))
      b ((left: LKProof, right: LKProof) =>
        InductionRule(
          InductionCase(left, hoc"nil: list", Nil, Nil, Suc(0)) ::
            InductionCase(right, hoc"cons:sk>list>list", Ant(0) :: Nil, hov"x_1:sk" :: hov"xs_1:list" :: Nil, Suc(1)) :: Nil,
          Abs(hov"zs:list", hof"B(zs:list):o"),
          hoc"t:list"
        )
      ) qed)
    Substitution(hov"x_0:sk" -> hov"x_1:sk", hov"xs_0" -> hov"xs_1")(proof)
    ok
  }
}
