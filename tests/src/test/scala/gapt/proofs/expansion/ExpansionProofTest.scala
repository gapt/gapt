package gapt.proofs.expansion

import gapt.cutintro.CutIntroduction
import gapt.examples.Pi2Pigeonhole
import gapt.expr._
import gapt.expr.subst.Substitution
import gapt.formats.ClasspathInputFile
import gapt.formats.llk.LLKProofParser
import gapt.logic.Polarity
import gapt.proofs.context.Context
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.lk.transformations.eliminateDefinitions
import gapt.proofs.{Sequent, SequentMatchers}
import gapt.provers.escargot.Escargot
import gapt.provers.verit.VeriT
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification
import gapt.examples.sequence.LinearExampleProof

class ExpansionProofTest extends Specification with SatMatchers with SequentMatchers {

  "linear example cut intro" in {
    val Some(p) = CutIntroduction(LinearExampleProof(6)): @unchecked
    val e = LKToExpansionProof(p)
    e.deep must beValidSequent
    eliminateCutsET(e).deep must beValidSequent
  }

  "reject cyclic proofs" in {
    ExpansionProof(Sequent() :+ ExpansionTree(hof"?x !y x=y", Polarity.InSuccedent, ETtWeak(hov"x" -> ETtStrong(hov"x", ETtAtom)))) must throwAn[IllegalArgumentException]
  }

  "substitute proofs" in {
    val proof = ExpansionProof(Sequent() :+ ExpansionTree(
      hof"∀x r(x,y)",
      Polarity.InSuccedent,
      ETtStrong(hov"x", ETtAtom)
    ))
    proof.deep must_== hos"⊢ r(x,y)"

    val proof1 = Substitution(hov"x" -> hov"y")(proof)
    proof1.deep must_== hos"⊢ r(x,y)"

    val proof2 = Substitution(hov"y" -> le"f(x)")(proof)
    val Seq(x0) = proof2.eigenVariables.toSeq
    proof2.deep must_== hos"⊢ r($x0, f(x))"
  }

  "pi2 pigeonhole" in {
    val e = LKToExpansionProof(Pi2Pigeonhole.proof)
    Escargot isValid e.deep must_== true
    Escargot isValid eliminateCutsET(e).deep must_== true
  }

  "tape proof cut elimination" in {
    val pdb = LLKProofParser(ClasspathInputFile("tape3ex.llk"))
    val lk = eliminateDefinitions(pdb.Definitions)(pdb proof "TAPEPROOF")
    val expansion = LKToExpansionProof(lk)
    val cutfree = eliminateCutsET(expansion)
    if (!VeriT.isInstalled) skipped
    VeriT isValid expansion.deep must_== true
    VeriT isValid cutfree.deep must_== true
  }

  "weird cuts" in {
    val epwc = ExpansionProof(ETCut(
      hof"∀x P(x)",
      ETtStrong(hov"x", ETtAtom),
      ETtWeak(le"f(x)" -> ETtAtom)
    ) +: Sequent() :+
      ExpansionTree(hof"∀x P(x) → ∃x P(f(x))", Polarity.InSuccedent, ETtBinary(ETtWeak(le"x" -> ETtAtom), ETtWeak(le"x" -> ETtAtom))))
    epwc.deep must beValidSequent
    val ep = eliminateCutsET(epwc)
    ep.deep must beValidSequent
  }

  "merge skolem and strong quantifiers" in {
    val ep = ExpansionProof(
      ExpansionTree(hof"∀x P(x)", Polarity.InAntecedent, ETtWeak(le"y" -> ETtAtom, le"sk" -> ETtAtom)) +:
        Sequent() :+ ExpansionTree(hof"∀x P(x)", Polarity.InSuccedent, ETtMerge(ETtStrong(hov"y", ETtAtom), ETtSkolem(le"sk", ETtAtom)))
    )
    ep.deep must beValidSequent
    val merged = eliminateMerges(ep)
    merged.deep must beValidSequent
    merged.subProofs foreach {
      case ETMerge(_, _) => ko
      case _             => ok
    }
    ok
  }

}

class ExpansionProofDefinitionEliminationTest extends Specification with SatMatchers {
  "simple unipolar definition" in {
    implicit var ctx = Context()
    ctx += Sort("i")
    ctx += hoc"P: i>o"
    ctx += hoc"f: i>i"
    ctx += hoc"c: i"
    ctx += hof"D x = (P x ∧ P (f x))"

    val d = ExpansionTree(
      hof"∀x (D x ↔ P x ∧ P (f x))",
      Polarity.InAntecedent,
      ETtWeak(le"c" -> ETtBinary(ETtBinary(ETtAtom, ETtBinary(ETtWeakening, ETtAtom)), ETtWeakening))
    )
    val f = ExpansionTree(
      hof"∃x (P x ∧ P (f x) → P (f x))",
      Polarity.InSuccedent,
      ETtWeak(le"c" -> ETtBinary(ETtDef(hof"D c", ETtAtom), ETtAtom))
    )

    val epwd = ExpansionProof(d +: Sequent() :+ f)
    epwd.deep must beValidSequent

    val epwc = eliminateDefsET(epwd, false, Set(hoc"D: i>o"))
    epwc.deep must beValidSequent

    val ep = eliminateCutsET(epwc)
    ep.deep must beValidSequent
  }
}
