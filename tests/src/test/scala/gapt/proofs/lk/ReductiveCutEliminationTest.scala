package gapt.proofs.lk

import gapt.expr._
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLAtomConst
import gapt.expr.formula.fol.FOLVar
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic.{Lemma, OpenAssumption, allL, andL, axiomLog, cut, impL, insert}
import gapt.proofs.lk.reductions._
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.InductionCase
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.lk.transformations.LeftRankInductionUnfoldingReduction
import gapt.proofs.lk.transformations.StuckCutReduction
import gapt.proofs.lk.transformations.acnf
import gapt.proofs.lk.transformations.acnfTop
import gapt.proofs.lk.transformations.cutNormal
import gapt.proofs.lk.transformations.isAcnf
import gapt.proofs.lk.transformations.isAcnfTop
import gapt.proofs.lk.util.isCutFree
import gapt.proofs.lk.util.isInductionFree
import gapt.proofs.{Ant, ProofBuilder, Sequent, SequentMatchers, Suc}
import gapt.provers.escargot.Escargot
import org.specs2.mutable._

class ReductiveCutEliminationTest extends Specification with SequentMatchers {

  "rank-reduction on strong quantifier rules" in {
    val p = FOLAtomConst("p", 1)
    val q = FOLAtom("q")
    val x = FOLVar("x")

    val proof = (ProofBuilder
      c LogicalAxiom(p(x))
      c LogicalAxiom(q)
      b (ImpLeftRule(_, Suc(0), _, Ant(0)))
      u (ForallLeftRule(_, Ant(0), p(x) --> q, x, x))
      u (ExistsLeftRule(_, Ant(1), x, x))

      c LogicalAxiom(q)
      c LogicalAxiom(p(x))
      b (ImpLeftRule(_, Suc(0), _, Ant(0)))

      b (CutRule(_, Suc(0), _, Ant(1))) qed)

    val proof_ = cutNormal(proof)

    proof_.endSequent must beMultiSetEqual(proof.endSequent)
  }
  "Testing ACNF check" in {
    val P1 = LogicalAxiom(fof"P")
    val P2 = LogicalAxiom(fof"P")
    val Proof = CutRule(P1, Suc(0), P2, Ant(0))
    isAcnf(Proof) mustEqual true
    isAcnfTop(Proof) mustEqual true

  }

  "Testing if not ACNF check" in {
    val Q1 = LogicalAxiom(fof"Q")
    val P1 = LogicalAxiom(fof"P")
    val P2 = LogicalAxiom(fof"P")
    val wQ = WeakeningLeftRule(P2, fof"Q")
    val PQ1 = AndRightRule(P1, fof"P", Q1, fof"Q")
    val PQ2 = AndLeftRule(wQ, fof"P", fof"Q")
    val Proof = CutRule(PQ1, Suc(0), PQ2, Ant(0))
    isAcnf(Proof) mustEqual false
    isAcnfTop(Proof) mustEqual false

  }

  "Testing not ACNF top check" in {
    val Q1 = LogicalAxiom(fof"Q")
    val P1 = LogicalAxiom(fof"P")
    val P2 = LogicalAxiom(fof"P")
    val PQ = OrLeftRule(P1, fof"P", Q1, fof"Q")
    val PQneg = NegLeftRule(PQ, fof"Q")
    val Proof = CutRule(PQneg, Suc(0), P2, Ant(0))
    isAcnfTop(Proof) mustEqual false

  }

  "Testing Conversion to ACNF" in {
    val Pa1 = LogicalAxiom(fof"P(a,1)")
    val Pa2 = LogicalAxiom(fof"P(a,2)")
    val Pb2 = LogicalAxiom(fof"P(b,2)")
    val Pa3 = LogicalAxiom(fof"P(a,3)")
    val Pb3 = LogicalAxiom(fof"P(b,3)")
    val R2 = LogicalAxiom(fof"R(2)")
    val R1 = LogicalAxiom(fof"R(1)")
    val R0 = LogicalAxiom(fof"R(0)")
    val Q2 = LogicalAxiom(fof"Q(2)")
    val Q1 = LogicalAxiom(fof"Q(1)")
    val Q0 = LogicalAxiom(fof"Q(0)")

    val Aux1_0 = ImpLeftRule(Pa2, fof"P(a,2)", Pa3, fof"P(a,3)")
    val Aux1_1 = NegRightRule(Aux1_0, fof"P(a,2)")
    val Aux1_2 = OrRightRule(Aux1_1, fof"-P(a,2)", fof"P(a,3)")

    val Aux2_0 = ImpLeftRule(Pb2, fof"P(b,2)", Pb3, fof"P(b,3)")
    val Aux2_1 = NegRightRule(Aux2_0, fof"P(b,2)")
    val Aux2_2 = OrRightRule(Aux2_1, fof"-P(b,2)", fof"P(b,3)")

    val C1_0 = NegRightRule(R0, fof"R(0)")
    val C1_1 = ImpLeftRule(C1_0, fof"-R(0)", Q0, fof"Q(0)")
    val C1_2 = NegLeftRule(Q2, fof"Q(2)")
    val C1_3 = WeakeningLeftRule(C1_2, fof"R(1)")
    val C1_4 = WeakeningLeftRule(C1_3, fof"-R(0)")
    val C1_5 = WeakeningLeftRule(C1_4, fof"((-Q(1))-> R(1))")
    val C1_6 = AndLeftRule(C1_5, fof"((-Q(1))-> R(1))", fof"Q(2)")
    val C1_7 = AndLeftRule(C1_6, fof"((-Q(1))-> R(1)) & Q(2) ", fof"-R(0)")
    val C1_8 = WeakeningRightRule(C1_7, fof"Q(1)")
    val C1_9 = AndRightRule(C1_1, fof"Q(0)", C1_8, fof"Q(1)")
    val C1_10 = AndLeftRule(C1_9, fof"((-R(0))-> Q(0))", fof"R(1)")
    val C1_11 = AndLeftRule(C1_10, fof"((-R(0))-> Q(0)) & R(1)", fof"-Q(2)")
    val C1_12 = NegRightRule(R1, fof"R(1)")
    val C1_13 = ImpLeftRule(C1_12, fof"-R(1)", Q1, fof"Q(1)")
    val C1_14 = NegLeftRule(R2, fof"R(2)")
    val C1_15 = WeakeningLeftRule(C1_14, fof"-Q(0)")
    val C1_16 = WeakeningLeftRule(C1_15, fof"Q(1)")
    val C1_17 = WeakeningLeftRule(C1_16, fof"((-Q(0))-> R(0))")
    val C1_18 = AndLeftRule(C1_17, fof"((-Q(0))-> R(0))", fof"Q(1)")
    val C1_19 = AndLeftRule(C1_18, fof"((-Q(0))-> R(0)) & Q(1) ", fof"-R(2)")
    val C1_20 = WeakeningRightRule(C1_19, fof"Q(0)")
    val C1_21 = AndRightRule(C1_20, fof"Q(0)", C1_13, fof"Q(1)")
    val C1_22 = AndLeftRule(C1_21, fof"((-R(1))-> Q(1))", fof"R(2)")
    val C1_23 = AndLeftRule(C1_22, fof"((-R(1))-> Q(1)) & R(2)", fof"-Q(0)")
    val C1_24 = ContractionRightRule(AndRightRule(C1_11, fof"R(0)", C1_23, fof"R(1)"), Suc(0), Suc(1))
    val C1_25 = OrRightRule(C1_24, fof"R(0) & R(1)", fof"Q(0) & Q(1)")
    val ProofC1 = AndRightRule(C1_25, fof"(R(0) & R(1)) | (Q(0) & Q(1))", Pa1, fof"P(a,1)")

    val C2_0 = NegRightRule(R1, fof"R(1)")
    val C2_1 = ImpLeftRule(C2_0, fof"-R(1)", Q1, fof"Q(1)")
    val C2_2 = NegLeftRule(Q0, fof"Q(0)")
    val C2_3 = WeakeningLeftRule(C2_2, fof"R(2)")
    val C2_4 = WeakeningLeftRule(C2_3, fof"-R(1)")
    val C2_5 = WeakeningLeftRule(C2_4, fof"((-Q(2))-> R(2))")
    val C2_6 = AndLeftRule(C2_5, fof"((-Q(2))-> R(2))", fof"Q(0)")
    val C2_7 = AndLeftRule(C2_6, fof"((-Q(2))-> R(2)) & Q(0) ", fof"-R(1)")
    val C2_8 = WeakeningRightRule(C2_7, fof"Q(2)")
    val C2_9 = AndRightRule(C2_1, fof"Q(1)", C2_8, fof"Q(2)")
    val C2_10 = AndLeftRule(C2_9, fof"((-R(1))-> Q(1))", fof"R(2)")
    val C2_11 = AndLeftRule(C2_10, fof"((-R(1))-> Q(1)) & R(2)", fof"-Q(0)")
    val C2_12 = NegRightRule(R2, fof"R(2)")
    val C2_13 = ImpLeftRule(C2_12, fof"-R(2)", Q2, fof"Q(2)")
    val C2_14 = NegLeftRule(Q1, fof"Q(1)")
    val C2_15 = WeakeningLeftRule(C2_14, fof"-R(2)")
    val C2_16 = WeakeningLeftRule(C2_15, fof"R(0)")
    val C2_17 = WeakeningLeftRule(C2_16, fof"((-Q(0))-> R(0))")
    val C2_18 = AndLeftRule(C2_17, fof"((-Q(0))-> R(0))", fof"Q(1)")
    val C2_19 = AndLeftRule(C2_18, fof"((-Q(0))-> R(0)) & Q(1) ", fof"-R(2)")
    val C2_20 = WeakeningRightRule(C2_19, fof"Q(1)")
    val C2_21 = AndRightRule(C2_20, fof"Q(1)", C2_13, fof"Q(2)")
    val C2_22 = AndLeftRule(C2_21, fof"((-R(2))-> Q(2))", fof"R(0)")
    val C2_23 = AndLeftRule(C2_22, fof"((-R(2))-> Q(2)) & R(0)", fof"-Q(1)")
    val C2_24 = ContractionRightRule(AndRightRule(C2_11, fof"R(1)", C2_23, fof"R(2)"), Suc(0), Suc(1))
    val C2_25 = OrRightRule(C2_24, fof"R(1) & R(2)", fof"Q(1) & Q(2)")
    val ProofC2 = AndRightRule(C2_25, fof"(R(1) & R(2)) | (Q(1) & Q(2))", Aux1_2, fof"-P(a,2) | P(a,3)")

    val C3_0 = NegRightRule(R0, fof"R(0)")
    val C3_1 = ImpLeftRule(C3_0, fof"-R(0)", Q0, fof"Q(0)")
    val C3_2 = NegLeftRule(Q2, fof"Q(2)")
    val C3_3 = WeakeningLeftRule(C3_2, fof"R(1)")
    val C3_4 = WeakeningLeftRule(C3_3, fof"-R(0)")
    val C3_5 = WeakeningLeftRule(C3_4, fof"((-Q(1))-> R(1))")
    val C3_6 = AndLeftRule(C3_5, fof"((-Q(1))-> R(1))", fof"Q(2)")
    val C3_7 = AndLeftRule(C3_6, fof"((-Q(1))-> R(1)) & Q(2) ", fof"-R(0)")
    val C3_8 = WeakeningRightRule(C3_7, fof"Q(2)")
    val C3_9 = AndRightRule(C3_1, fof"Q(0)", C3_8, fof"Q(2)")
    val C3_10 = AndLeftRule(C3_9, fof"((-R(0))-> Q(0))", fof"R(1)")
    val C3_11 = AndLeftRule(C3_10, fof"((-R(0))-> Q(0)) & R(1)", fof"-Q(2)")
    val C3_12 = NegRightRule(R2, fof"R(2)")
    val C3_13 = ImpLeftRule(C3_12, fof"-R(2)", Q2, fof"Q(2)")
    val C3_14 = NegLeftRule(Q1, fof"Q(1)")
    val C3_15 = WeakeningLeftRule(C3_14, fof"R(0)")
    val C3_16 = WeakeningLeftRule(C3_15, fof"-R(2)")
    val C3_17 = WeakeningLeftRule(C3_16, fof"((-Q(0))-> R(0))")
    val C3_18 = AndLeftRule(C3_17, fof"((-Q(0))-> R(0))", fof"Q(1)")
    val C3_19 = AndLeftRule(C3_18, fof"((-Q(0))-> R(0)) & Q(1) ", fof"-R(2)")
    val C3_20 = WeakeningRightRule(C3_19, fof"Q(0)")
    val C3_21 = AndRightRule(C3_20, fof"Q(0)", C3_13, fof"Q(2)")
    val C3_22 = AndLeftRule(C3_21, fof"((-R(2))-> Q(2))", fof"R(0)")
    val C3_23 = AndLeftRule(C3_22, fof"((-R(2))-> Q(2)) & R(0)", fof"-Q(1)")
    val C3_24 = ContractionRightRule(AndRightRule(C3_11, fof"R(0)", C3_23, fof"R(2)"), Suc(0), Suc(1))
    val C3_25 = OrRightRule(C3_24, fof"R(0) & R(2)", fof"Q(0) & Q(2)")
    val ProofC3 = AndRightRule(C3_25, fof"(R(0) & R(2)) | (Q(0) & Q(2))", Aux2_2, fof"-P(b,2) | P(b,3)")

    val Pa1AndR1 = AndRightRule(Pa1, fof"P(a,1)", R1, fof"R(1)")
    val Pa1AndR1AndR0 = AndRightRule(Pa1AndR1, fof"P(a,1) & R(1)", R0, fof"R(0)")
    val Pa1AndQ1 = AndRightRule(Pa1, fof"P(a,1)", Q1, fof"Q(1)")
    val Pa1AndQ1AndQ0 = AndRightRule(Pa1AndQ1, fof"P(a,1) & Q(1)", Q0, fof"Q(0)")
    val Pa3AndR1 = AndRightRule(Pa3, fof"P(a,3)", R1, fof"R(1)")
    val Pa3AndQ1 = AndRightRule(Pa3, fof"P(a,3)", Q1, fof"Q(1)")
    val Pb3AndR0 = AndRightRule(Pb3, fof"P(b,3)", R0, fof"R(0)")
    val Pb3AndQ0 = AndRightRule(Pb3, fof"P(b,3)", Q0, fof"Q(0)")
    val Pa3AndR1AndR2 = AndRightRule(Pa3AndR1, fof"P(a,3) & R(1)", R2, fof"R(2)")
    val Pa3AndQ1AndQ2 = AndRightRule(Pa3AndQ1, fof"P(a,3) & Q(1)", Q2, fof"Q(2)")
    val Pb3AndR0AndR2 = AndRightRule(Pb3AndR0, fof"P(b,3) & R(0)", R2, fof"R(2)")
    val Pb3AndQ0AndQ2 = AndRightRule(Pb3AndQ0, fof"P(b,3) & Q(0)", Q2, fof"Q(2)")
    val ProofCutR01 = AndLeftRule(Pa1AndR1AndR0, fof"R(0)", fof"R(1)")
    val ProofCutQ01 = AndLeftRule(Pa1AndQ1AndQ0, fof"Q(0)", fof"Q(1)")
    val ProofCutR12 = AndLeftRule(Pa3AndR1AndR2, fof"R(1)", fof"R(2)")
    val ProofCutQ12 = AndLeftRule(Pa3AndQ1AndQ2, fof"Q(1)", fof"Q(2)")
    val ProofCutR02 = AndLeftRule(Pb3AndR0AndR2, fof"R(0)", fof"R(2)")
    val ProofCutQ02 = AndLeftRule(Pb3AndQ0AndQ2, fof"Q(0)", fof"Q(2)")
    val Pa2NegCons = NegLeftRule(Pa2, fof"P(a,2)")
    val Pb2NegCons = NegLeftRule(Pb2, fof"P(b,2)")
    val ProofCutR02Q02 = OrLeftRule(ProofCutR02, fof"R(0) & R(2)", ProofCutQ02, fof"Q(0) & Q(2)")
    val ProofCutR01Q01 = OrLeftRule(ProofCutR01, fof"R(0) & R(1)", ProofCutQ01, fof"Q(0) & Q(1)")
    val ProofCutR12Q12 = OrLeftRule(ProofCutR12, fof"R(1) & R(2)", ProofCutQ12, fof"Q(1) & Q(2)")
    val ProofCutR01Q01WLPb2 = WeakeningLeftRule(ProofCutR01Q01, fof"-P(b,2)")
    val ProofCutR01Q01R02Q02 = OrLeftRule(ProofCutR01Q01WLPb2, fof"-P(b,2)", ProofCutR02Q02, fof"P(b,3)")
    val ProofCutR01Q01R02Q02WPa2 = WeakeningLeftRule(ProofCutR01Q01R02Q02, fof"-P(a,2)")
    val ProofCutR01Q01R02Q02R12Q12 = OrLeftRule(ProofCutR01Q01R02Q02WPa2, fof"-P(a,2)", ProofCutR12Q12, fof"P(a,3)")
    val ProofCutR01Q01R02Q02R12Q12WithNegPa2 = OrLeftRule(Pa2NegCons, fof"-P(a,2)", ProofCutR01Q01R02Q02R12Q12, fof"P(a,3)")
    val ProofCutR01Q01R02Q02R12Q12WithNegPa2WithNegPb2 = OrLeftRule(Pb2NegCons, fof"-P(b,2)", ProofCutR01Q01R02Q02R12Q12WithNegPa2, fof"P(b,3)")
    val ProofCutR01Q01R02Q02R12Q12WithNegPa2WithNegPb2WCb = ContractionLeftRule(ProofCutR01Q01R02Q02R12Q12WithNegPa2WithNegPb2, Ant(0), Ant(5))
    val ProofCutR01Q01R02Q02R12Q12WithNegPa2WithNegPb2WCbWCa = ContractionLeftRule(ProofCutR01Q01R02Q02R12Q12WithNegPa2WithNegPb2WCb, Ant(2), Ant(4))
    val ProofCutR01Q01R02Q02R12Q12WithNegPa2WithNegPb2WCbWCaW1a = ContractionLeftRule(ProofCutR01Q01R02Q02R12Q12WithNegPa2WithNegPb2WCbWCa, Ant(5), Ant(6))
    val ProofWithC1 = AndLeftRule(ProofCutR01Q01R02Q02R12Q12WithNegPa2WithNegPb2WCbWCaW1a, fof"(R(0) & R(1)) | (Q(0) & Q(1))", fof"P(a,1)")
    val ProofWithC1C2 = AndLeftRule(ProofWithC1, fof"(R(1) & R(2)) | (Q(1) & Q(2))", fof"-P(a,2) | P(a,3)")
    val ProofWithC1C2C3 = AndLeftRule(ProofWithC1C2, fof"(R(0) & R(2)) | (Q(0) & Q(2))", fof"-P(b,2) | P(b,3)")
    val ProofWithC1C2C3E1 = OrRightRule(ProofWithC1C2C3, fof"(P(a,1) & R(1) & R(0))", fof"(P(a,1) & Q(1) & Q(0))")
    val ProofWithC1C2C3E1E2 = OrRightRule(ProofWithC1C2C3E1, fof"(P(a,3) & R(1) & R(2))", fof"(P(a,3) & Q(1) & Q(2))")
    val ProofWithC1C2C3E1E2E3 = OrRightRule(ProofWithC1C2C3E1E2, fof"(P(b,3) & R(0) & R(2))", fof"(P(b,3) & Q(0) & Q(2))")
    val ProofWithC1C2C3E1E2E3withImp1 = ImpRightRule(ProofWithC1C2C3E1E2E3, fof"P(b,2)", fof"(P(b,3) & R(0) & R(2)) | (P(b,3) & Q(0) & Q(2))")
    val LeftProofComp = ImpRightRule(ProofWithC1C2C3E1E2E3withImp1, fof"P(a,2)", fof"(P(a,3) & R(1) & R(2)) | (P(a,3) & Q(1) & Q(2))")
    val ProofFinC1 = CutRule(ProofC1, Suc(0), LeftProofComp, Ant(2))
    val ProofFinC1C2 = CutRule(ProofC2, Suc(0), ProofFinC1, Ant(6))
    val Proof: LKProof = CutRule(ProofC3, Suc(0), ProofFinC1C2, Ant(10))

    val ACNFProof = acnf(Proof)
    val ACNFTopProof = acnfTop(Proof)
    isAcnfTop(ACNFProof) mustEqual false
    isAcnfTop(ACNFTopProof) mustEqual true
    isAcnf(ACNFTopProof) mustEqual true
  }

  "right cut formula introduced by weakening" in {
    val proof = (ProofBuilder
      c LogicalAxiom(hof"D")
      u (WeakeningRightRule(_, hof"A"))
      c LogicalAxiom(hof"B")
      u (WeakeningRightRule(_, hof"C"))
      u (WeakeningLeftRule(_, hof"A"))
      b (CutRule(_, _, hof"A")) qed)
    val cut = proof.asInstanceOf[CutRule]

    rightRankReduction(cut).get.endSequent must beMultiSetEqual(cut.endSequent)
  }

  "left cut formula introduced by weakening" in {
    val proof = (ProofBuilder
      c LogicalAxiom(hof"B")
      u (WeakeningRightRule(_, hof"A"))
      c LogicalAxiom(hof"C")
      u (WeakeningLeftRule(_, hof"A"))
      b (CutRule(_, _, hof"A")) qed)
    val cut = proof.asInstanceOf[CutRule]

    gradeReduction(cut).get.endSequent must beMultiSetEqual(cut.endSequent)
  }

  "induction left rank reduction should lift cut over induction" in {
    implicit var context: Context = Context()
    context += InductiveType("nat", hoc"0: nat", hoc"s:nat>nat")
    context += hoc"equal: nat>nat>o"
    context += hoc"le: nat>nat>o"
    context += hoc"A:o"
    context += hoc"F:nat>o"

    val proof = (ProofBuilder
      c LogicalAxiom(hof"A")
      u (WeakeningRightRule(_, hof"F(0)"))
      c LogicalAxiom(hof"A")
      u (WeakeningLeftRule(_, hof"F(x)"))
      u (WeakeningRightRule(_, hof"F(s(x))"))
      b ((ib, ic) =>
        InductionRule(
          InductionCase(ib, hoc"0:nat", Nil, Nil, Suc(1)) ::
            InductionCase(ic, hoc"s:nat>nat", Ant(0) :: Nil, hov"x:nat" :: Nil, Suc(1)) :: Nil,
          Abs(hov"x:nat", le"F(x)"),
          hov"x:nat"
        )
      )
      c LogicalAxiom(hof"A")
      b (CutRule(_, _, hof"A")) qed)
    val reduced = LeftRankInductionReduction(proof.asInstanceOf[CutRule]).get

    if (!reduced.endSequent.multiSetEquals(proof.endSequent)) {
      failure("the reduced proof does not prove the same end-sequent")
    }
    reduced match {
      case InductionRule(InductionCase(CutRule(_, _, _, _), _, _, _, _) :: _ :: Nil, _, _) => success
      case _                                                                               => failure("the proof has not been reduced as expected")
    }
  }
  "induction right rank reduction should lift cut over induction" in {
    implicit var context: Context = Context()
    context += InductiveType("nat", hoc"0: nat", hoc"s:nat>nat")
    context += hoc"equal: nat>nat>o"
    context += hoc"le: nat>nat>o"
    context += hoc"A:o"
    context += hoc"F:nat>o"

    val proof = (ProofBuilder
      c LogicalAxiom(hof"A")
      c LogicalAxiom(hof"A")
      u (WeakeningRightRule(_, hof"F(0)"))
      c LogicalAxiom(hof"A")
      u (WeakeningLeftRule(_, hof"F(x)"))
      u (WeakeningRightRule(_, hof"F(s(x))"))
      b ((ib, ic) =>
        InductionRule(
          InductionCase(ib, hoc"0:nat", Nil, Nil, Suc(1)) ::
            InductionCase(ic, hoc"s:nat>nat", Ant(0) :: Nil, hov"x:nat" :: Nil, Suc(1)) :: Nil,
          Abs(hov"x:nat", le"F(x)"),
          hov"x:nat"
        )
      )
      b (CutRule(_, _, hof"A")) qed)
    val reduced = RightRankInductionReduction(proof.asInstanceOf[CutRule]).get

    if (!reduced.endSequent.multiSetEquals(proof.endSequent)) {
      failure("the reduced proof does not prove the same end-sequent")
    }
    reduced match {
      case InductionRule(InductionCase(CutRule(_, _, _, _), _, _, _, _) :: _ :: Nil, _, _) => success
      case _                                                                               => failure("the proof has not been reduced as expected")
    }
  }

  "(1) free cut elimination should eliminate free cuts" in {
    implicit val context = MutableContext.default()
    context += InductiveType("nat", hoc"0: nat", hoc"s:nat>nat")
    context += hoc"equal: nat>nat>o"
    context += hoc"le: nat>nat>o"

    val axioms = Seq(
      "ae1" -> hof"equal(0, 0)",
      "ae4" -> hof"∀x2 ∀y2 ((equal(s(x2), s(y2)) → equal(x2, y2)) ∧ (equal(x2, y2) → equal(s(x2), s(y2))))",
      "al1" -> hof"∀y le(0, y)",
      "al3" -> hof"∀z ∀x2 ((le(s(z), s(x2)) → le(z, x2)) ∧ (le(z, x2) → le(s(z), s(x2))))",
      "ael" -> hof"!x !y (equal(x,y) → le(x,y))"
    )

    val baseCase = Lemma(axioms ++: Sequent() :+ ("goal" -> hof"equal(0,0)")) {
      axiomLog
    }
    val indCase = Lemma(("ih" -> hof"equal(x_0,x_0)") +: axioms ++: Sequent() :+ ("goal" -> hof"equal(s(x_0),s(x_0))")) {
      allL("ae4", le"x_0:nat", le"x_0:nat")
      andL
      impL("ae4_0_1")
      axiomLog
      axiomLog
    }

    val inductivePart = InductionRule(
      InductionCase(baseCase, hoc"0:nat", Nil, Nil, Suc(0)) ::
        InductionCase(indCase, hoc"s:nat>nat", Ant(5) :: Nil, hov"x_0:nat" :: Nil, Suc(0)) :: Nil,
      Abs(hov"x:nat", le"equal(x,x)"),
      le"s(s(s(0)))"
    )

    val proof = Lemma(axioms ++: Sequent() :+ ("goal" -> hof"le(s(s(s(0))), s(s(s(0))))")) {
      cut("ip", hof"equal(s(s(s(0))), s(s(s(0))) )")
      insert(inductivePart)
      allL("ael", le"s(s(s(0)))", le"s(s(s(0)))")
      impL("ael_0")
      axiomLog
      axiomLog
    }

    val cutFree = cutNormal(proof)

    if (!isCutFree(cutFree)) {
      failure("the generated proof is not cut free")
    }
    if (!cutFree.endSequent.multiSetEquals(proof.endSequent)) {
      failure("the generated proof does not prove the same end-sequent")
    }
    success
  }

  "reduce cut with left-equality as left upper sequent " in {
    val proof = (ProofBuilder
      c LogicalAxiom(hof"P(b)")
      u (WeakeningLeftRule(_, hof"a = b"))
      u (EqualityLeftRule(_, Ant(0), Ant(1), Abs(hov"x", le"P(x):o")))
      c OpenAssumption(Sequent(("" -> hof"P(b)") :: Nil, ("" -> hof"F") :: Nil))
      b (CutRule(_, _, hof"P(b)")) qed)
    val reduction = leftRankReduction(proof.asInstanceOf[CutRule]).get
    proof.conclusion must beSetEqual(reduction.conclusion)
  }

  "reduce cut with right-equality as left upper sequent" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent(Nil, "" -> hof"P(b)" :: Nil))
      u (WeakeningLeftRule(_, hof"a = b"))
      u (WeakeningRightRule(_, hof"B"))
      u (EqualityRightRule(_, Ant(0), Suc(0), Abs(hov"x", le"P(x):o")))
      c OpenAssumption(Sequent(("" -> hof"B") :: Nil, ("" -> hof"F") :: Nil))
      b (CutRule(_, _, hof"B")) qed)
    val reduction = leftRankReduction(proof.asInstanceOf[CutRule]).get
    proof.conclusion must beSetEqual(reduction.conclusion)
  }

  "reduce cut with left-equality as right upper sequent" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent(Nil, ("" -> hof"A") :: Nil))
      c OpenAssumption(Sequent("" -> hof"A" :: "" -> hof"a = b" :: "" -> hof"P(b)" :: Nil, Nil))
      u (EqualityLeftRule(_, Ant(1), Ant(2), Abs(hov"x", le"P(x):o")))
      b (CutRule(_, _, hof"A")) qed)
    val reduction = rightRankReduction(proof.asInstanceOf[CutRule]).get
    proof.conclusion must beSetEqual(reduction.conclusion)
  }

  "reduce cut with left-equality as right proof on the cut formula" in {
    val proof = (ProofBuilder
      .c( OpenAssumption(Sequent() :+ ("" -> hof"A(s)")))
      .c( OpenAssumption(Sequent() :+ ("" -> hof"B(s)")))
      .b((p1, p2) => AndRightRule(p1, p2, hof"A(s) & B(s)"))

      .c(OpenAssumption(("" -> hof"t = s") +: ("" -> hof"A(t)") +: ("" -> hof"B(t)") +: Sequent()))
      .u(p => AndLeftRule(p, hof"A(t) & B(t)"))
      .u(p => EqualityLeftRule(p, hof"t = s", hof"A(t) & B(t)", hof"A(s) & B(s)"))

      .b((p1, p2) => CutRule(p1, p2, hof"A(s) & B(s)"))
      qed)
    val acnf = cutNormal(proof)
    isAcnf(acnf) must beTrue
  }

  "reduce cut with right-equality as left proof on the cut formula" in {
    val proof = (ProofBuilder
      .c(OpenAssumption(Sequent() :+ ("" -> hof"A(t)")))
      .c(OpenAssumption(Sequent() :+ ("" -> hof"B(t)")))
      .b((p1, p2) => AndRightRule(p1, p2, hof"A(t) & B(t)"))
      .u(p => WeakeningLeftRule(p, hof"s = t"))
      .u(p => EqualityRightRule(p, hof"s = t", hof"A(t) & B(t)", hof"A(s) & B(s)"))

      .c(OpenAssumption(("" -> hof"A(s)") +: ("" -> hof"B(s)") +: Sequent()))
      .u(p => AndLeftRule(p, hof"A(s) & B(s)"))

      .b((p1, p2) => CutRule(p1, p2, hof"A(s) & B(s)"))
      qed)
    val acnf = cutNormal(proof)
    isAcnf(acnf) must beTrue
  }

  "reduce cut with right-equality as right upper sequent" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent(Nil, ("" -> hof"A") :: Nil))
      c OpenAssumption(Sequent("" -> hof"A" :: "" -> hof"a = b" :: Nil, "" -> hof"P(b)" :: Nil))
      u (EqualityRightRule(_, Ant(1), Suc(0), Abs(hov"x", le"P(x):o")))
      b (CutRule(_, _, hof"A")) qed)
    val reduction = rightRankReduction(proof.asInstanceOf[CutRule]).get
    proof.conclusion must beSetEqual(reduction.conclusion)
  }

  "right rank reduction: forall right" in {
    val proof = (ProofBuilder
      c LogicalAxiom(hof"C(x)")
      u (WeakeningRightRule(_, hof"B"))
      c (LogicalAxiom(hof"D"))
      u (WeakeningRightRule(_, hof"A(x)"))
      u (WeakeningLeftRule(_, hof"B"))
      u (ForallRightRule(_, hof"!x A(x)"))
      b (CutRule(_, _, hof"B")) qed)
    val reducedProof = rightRankReduction(proof.asInstanceOf[CutRule]).get
    proof.conclusion must beMultiSetEqual(reducedProof.conclusion)
  }

  "right rank reduction: exists left" in {
    val proof = (ProofBuilder
      c LogicalAxiom(hof"C(x)")
      u (WeakeningRightRule(_, hof"B"))
      c (LogicalAxiom(hof"D"))
      u (WeakeningLeftRule(_, hof"A(x)"))
      u (WeakeningLeftRule(_, hof"B"))
      u (ExistsLeftRule(_, hof"?x A(x)"))
      b (CutRule(_, _, hof"B")) qed)
    val reducedProof = rightRankReduction(proof.asInstanceOf[CutRule]).get
    proof.conclusion must beMultiSetEqual(reducedProof.conclusion)
  }

  "left rank reduction: forall right" in {
    val proof = (ProofBuilder
      c LogicalAxiom(hof"B")
      u (WeakeningRightRule(_, hof"F"))
      u (WeakeningRightRule(_, hof"A(x)"))
      u (ForallRightRule(_, hof"!x A(x)"))
      c (LogicalAxiom(hof"C(x)"))
      u (WeakeningLeftRule(_, hof"F"))
      b (CutRule(_, _, hof"F")) qed)
    val reducedProof = leftRankReduction(proof.asInstanceOf[CutRule]).get
    proof.conclusion must beMultiSetEqual(reducedProof.conclusion)
  }

  "left rank reduction: exists left" in {
    val proof = (ProofBuilder
      c LogicalAxiom(hof"B")
      u (WeakeningLeftRule(_, hof"A(x)"))
      u (ExistsLeftRule(_, hof"?x A(x)"))
      c (LogicalAxiom(hof"C(x)"))
      u (WeakeningLeftRule(_, hof"B"))
      b (CutRule(_, _, hof"B")) qed)
    val reducedProof = leftRankReduction(proof.asInstanceOf[CutRule]).get
    reducedProof.conclusion must beMultiSetEqual(proof.conclusion)
  }

  "grade reduction with equality inferences having the same auxiliary formula" in {
    val proof = (ProofBuilder
      c OpenAssumption(("" -> hof"s = t") +: Sequent() :+ ("" -> hof"A(s)"))
      u (EqualityRightRule(_, Ant(0), Suc(0), Abs(hov"x", le"A(x):o")))
      c OpenAssumption(("" -> hof"s = t") +: ("" -> hof"A(s)") +: Sequent())
      u (EqualityLeftRule(_, Ant(0), Ant(1), Abs(hov"x", le"A(x):o")))
      b (CutRule(_, _, hof"A(t)")) qed)
    val reduction = gradeReduction(proof.asInstanceOf[CutRule]).get
    proof.conclusion must beMultiSetEqual(reduction.conclusion)
    reduction.subProofAt(0 :: Nil) must beAnInstanceOf[OpenAssumption]
  }

  "issue 684" in {
    val Some(p) = Escargot.getLKProof(hof"¬(∀x x = c0 ∧ ∃x f0(x) != f1(x))"): @unchecked
    val q = cutNormal(p)
    ok
  }

  "cut left equality-right left" in {
    val proof = (ProofBuilder
      c OpenAssumption(("" -> hof"s=t") +: Sequent() :+ ("" -> hof"B(s)") :+ ("" -> hof"A"))
      u (EqualityRightRule(_, Ant(0), Suc(0), Abs(hov"x", le"B(x):o")))
      c OpenAssumption(("" -> hof"B(t)") +: Sequent())
      b (CutRule(_, _, hof"B(t)"))
      c OpenAssumption(("" -> hof"A") +: Sequent())
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Left.reduce(proof): @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 0 :: Nil) must beAnInstanceOf[CutRule]
  }

  "cut left equality-right right should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(("" -> hof"s=t") +: Sequent() :+ ("" -> hof"B(s)") :+ ("" -> hof"A"))
      u (EqualityRightRule(_, Ant(0), Suc(0), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"s=t"))
      c OpenAssumption(("" -> hof"A") +: Sequent())
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Left.reduce(proof): @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 1 :: Nil) must beAnInstanceOf[CutRule]
  }

  "cut left equality-left right should not reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(("" -> hof"s=t") +: Sequent() :+ ("" -> hof"B(s)") :+ ("" -> hof"A"))
      u (EqualityRightRule(_, Ant(0), Suc(0), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"s=t"))
      c OpenAssumption(("" -> hof"B(t)") +: Sequent())
      b (CutRule(_, _, hof"B(t)")) qed)
    StuckCutReduction.Left.reduce(proof).isEmpty must_== true
  }

  "cut left equality-left left should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(("" -> hof"s=t") +: ("" -> hof"B(s)") +: Sequent() :+ ("" -> hof"A"))
      u (EqualityLeftRule(_, Ant(0), Ant(1), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"s=t"))
      c OpenAssumption(("" -> hof"A") +: Sequent())
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Left reduce proof: @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 1 :: Nil) must beAnInstanceOf[CutRule]
  }

  "cut right equality-left right should not reduce 1" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"B(t)"))
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(("" -> hof"s=t") +: ("" -> hof"B(s)") +: Sequent())
      u (EqualityLeftRule(_, Ant(0), Ant(1), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"s=t"))
      b (CutRule(_, _, hof"B(t)")) qed)
    StuckCutReduction.Right.reduce(proof).isEmpty must_== true
  }

  "cut right equality-left right should not reduce 2" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(Sequent() :+ ("" -> hof"B(t)"))
      c OpenAssumption(("" -> hof"s=t") +: ("" -> hof"B(s)") +: Sequent())
      u (EqualityLeftRule(_, Ant(0), Ant(1), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"B(t)"))
      b (CutRule(_, _, hof"s=t")) qed)
    StuckCutReduction.Right.reduce(proof).isEmpty must_== true
  }

  "cut right equality-left right should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"A"))
      c OpenAssumption(Sequent() :+ ("" -> hof"B(t)"))
      c OpenAssumption(("" -> hof"A") +: ("" -> hof"s=t") +: ("" -> hof"B(s)") +: Sequent())
      u (EqualityLeftRule(_, Ant(1), Ant(2), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"B(t)"))
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Right reduce proof: @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 1 :: Nil) must beAnInstanceOf[CutRule]
  }

  "cut right equality-right left should not reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(("" -> hof"s=t") +: Sequent() :+ ("" -> hof"B(s)"))
      u (EqualityRightRule(_, Ant(0), Suc(0), Abs(hov"x", le"B(x):o")))
      c OpenAssumption(("" -> hof"B(t)") +: Sequent())
      b (CutRule(_, _, hof"B(t)"))
      b (CutRule(_, _, hof"s=t")) qed)
    StuckCutReduction.Right.reduce(proof).isEmpty must_== true
  }

  "cut right equality-right left should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"A"))
      c OpenAssumption(("" -> hof"A") +: ("" -> hof"s=t") +: Sequent() :+ ("" -> hof"B(s)"))
      u (EqualityRightRule(_, Ant(1), Suc(0), Abs(hov"x", le"B(x):o")))
      c OpenAssumption(("" -> hof"B(t)") +: Sequent())
      b (CutRule(_, _, hof"B(t)"))
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Right reduce proof: @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 0 :: Nil) must beAnInstanceOf[CutRule]
  }

  "cut right equality-right right should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"A"))
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(("" -> hof"A") +: ("" -> hof"s=t") +: Sequent() :+ ("" -> hof"B(s)"))
      u (EqualityRightRule(_, Ant(1), Suc(0), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"s=t"))
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Right reduce proof: @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 1 :: Nil) must beAnInstanceOf[CutRule]
  }

  "left cut cut equality-right 1 should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(("" -> hof"s=t") +: Sequent() :+ ("" -> hof"B(s)") :+ ("" -> hof"A"))
      u (EqualityRightRule(_, Ant(0), Suc(0), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"s=t"))
      c OpenAssumption(("" -> hof"B(t)") +: Sequent())
      b (CutRule(_, _, hof"B(t)"))
      c OpenAssumption(("" -> hof"A") +: Sequent())
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Left.reduce(proof): @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 1 :: 0 :: Nil) must beAnInstanceOf[CutRule]
  }

  "left cut cut equality-right 2 should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(("" -> hof"s=t") +: Sequent() :+ ("" -> hof"B(s)") :+ ("" -> hof"A"))
      u (EqualityRightRule(_, Ant(0), Suc(0), Abs(hov"x", le"B(x):o")))
      c OpenAssumption(("" -> hof"B(t)") +: Sequent())
      b (CutRule(_, _, hof"B(t)"))
      b (CutRule(_, _, hof"s=t"))
      c OpenAssumption(("" -> hof"A") +: Sequent())
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Left.reduce(proof): @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 0 :: 1 :: Nil) must beAnInstanceOf[CutRule]
  }

  "left cut cut equality-left should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"B(t)"))
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(("" -> hof"s=t") +: ("" -> hof"B(s)") +: Sequent() :+ ("" -> hof"A"))
      u (EqualityLeftRule(_, Ant(0), Ant(1), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"s=t"))
      b (CutRule(_, _, hof"B(t)"))
      c OpenAssumption(("" -> hof"A") +: Sequent())
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Left.reduce(proof): @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 1 :: 1 :: Nil) must beAnInstanceOf[CutRule]
  }

  "right cut cut equality-left should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"A"))
      c OpenAssumption(Sequent() :+ ("" -> hof"B(t)"))
      c OpenAssumption(Sequent() :+ ("" -> hof"s=t"))
      c OpenAssumption(("" -> hof"s=t") +: ("" -> hof"B(s)") +: ("" -> hof"A") +: Sequent())
      u (EqualityLeftRule(_, Ant(0), Ant(1), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"s=t"))
      b (CutRule(_, _, hof"B(t)"))
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Right.reduce(proof): @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 1 :: 1 :: Nil) must beAnInstanceOf[CutRule]
  }

  "right cut cut equality-right 1 should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"A"))
      c OpenAssumption(Sequent() :+ ("" -> hof"s = t"))
      c OpenAssumption(("" -> hof"A") +: ("" -> hof"s=t") +: Sequent() :+ ("" -> hof"B(s)"))
      u (EqualityRightRule(_, Ant(1), Suc(0), Abs(hov"x", le"B(x):o")))
      c OpenAssumption(("" -> hof"B(t)") +: Sequent())
      b (CutRule(_, _, hof"B(t)"))
      b (CutRule(_, _, hof"s=t"))
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Right.reduce(proof): @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 0 :: 1 :: Nil) must beAnInstanceOf[CutRule]
  }

  "right cut cut equality-right 2 should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"A"))
      c OpenAssumption(Sequent() :+ ("" -> hof"s = t"))
      c OpenAssumption(("" -> hof"A") +: ("" -> hof"s=t") +: Sequent() :+ ("" -> hof"B(s)"))
      u (EqualityRightRule(_, Ant(1), Suc(0), Abs(hov"x", le"B(x):o")))
      b (CutRule(_, _, hof"s=t"))
      c OpenAssumption(("" -> hof"B(t)") +: Sequent())
      b (CutRule(_, _, hof"B(t)"))
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Right.reduce(proof): @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 1 :: 0 :: Nil) must beAnInstanceOf[CutRule]
  }

  "stuck cut left forall-sk should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"A(s)") :+ ("" -> hof"B"))
      u (ForallSkRightRule(_, Suc(0), hof"!x A(x)", le"s"))
      c OpenAssumption(("" -> hof"!x A(x)") +: Sequent())
      b (CutRule(_, _, hof"!x A(x)"))
      c OpenAssumption(("" -> hof"B") +: Sequent())
      b (CutRule(_, _, hof"B")) qed)
    val Some(newProof) = StuckCutReduction.Left reduce proof: @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 0 :: Nil) must beAnInstanceOf[CutRule]
  }

  "stuck cut left exists-sk should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"?x A(x)"))
      c OpenAssumption(("" -> hof"A(s)") +: Sequent() :+ ("" -> hof"B"))
      u (ExistsSkLeftRule(_, Ant(0), hof"?x A(x)", le"s"))
      b (CutRule(_, _, hof"?x A(x)"))
      c OpenAssumption(("" -> hof"B") +: Sequent())
      b (CutRule(_, _, hof"B")) qed)
    val Some(newProof) = StuckCutReduction.Left reduce proof: @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 1 :: Nil) must beAnInstanceOf[CutRule]
  }

  "stuck cut right forall-sk should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"B"))
      c OpenAssumption(("" -> hof"B") +: Sequent() :+ ("" -> hof"A(s)"))
      u (ForallSkRightRule(_, Suc(0), hof"!x A(x)", le"s"))
      c OpenAssumption(("" -> hof"!x A(x)") +: Sequent())
      b (CutRule(_, _, hof"!x A(x)"))
      b (CutRule(_, _, hof"B")) qed)
    val Some(newProof) = StuckCutReduction.Right reduce proof: @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 0 :: Nil) must beAnInstanceOf[CutRule]
  }

  "stuck cut right exists-sk should reduce" in {
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"B"))
      c OpenAssumption(Sequent() :+ ("" -> hof"?x A(x)"))
      c OpenAssumption(("" -> hof"B") +: ("" -> hof"A(s)") +: Sequent())
      u (ExistsSkLeftRule(_, Ant(1), hof"?x A(x)", le"s"))
      b (CutRule(_, _, hof"?x A(x)"))
      b (CutRule(_, _, hof"B")) qed)
    val Some(newProof) = StuckCutReduction.Right reduce proof: @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(0 :: 1 :: Nil) must beAnInstanceOf[CutRule]
  }

  "left rank induction unfolding reduction should reduce" in {
    implicit var context: Context = Context()
    context += InductiveType("nat", hoc"0: nat", hoc"s:nat>nat")
    context += hoc"F:nat>o"
    context += hoc"A:o"
    val proof = (ProofBuilder
      c LogicalAxiom(hof"F(0)")
      c LogicalAxiom(hof"A")
      u (WeakeningLeftRule(_, hof"F(x)"))
      u (WeakeningRightRule(_, hof"F(s(x))"))
      b ((base, step) => {
        InductionRule(
          InductionCase(base, hoc"0:nat", Nil, Nil, Suc(0)) ::
            InductionCase(step, hoc"s:nat>nat", Ant(0) :: Nil, hov"x:nat" :: Nil, Suc(1)) ::
            Nil,
          Abs(hov"x:nat", le"F(x)"),
          le"s(s(0))"
        )
      })
      c OpenAssumption(("" -> hof"F(s(s(0)))") +: Sequent())
      b (CutRule(_, _, hof"F(s(s(0)))")) qed)
    val Some(newProof) = new LeftRankInductionUnfoldingReduction reduce proof: @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    isInductionFree(newProof) must_== true
  }

  "left rank cut induction should reduce" in {
    implicit var context: Context = Context()
    context += InductiveType("nat", hoc"0: nat", hoc"s:nat>nat")
    context += hoc"F:nat>o"
    context += hoc"A:o"
    val proof = (ProofBuilder
      c LogicalAxiom(hof"F(0)")
      c LogicalAxiom(hof"A")
      u (WeakeningLeftRule(_, hof"F(x)"))
      u (WeakeningRightRule(_, hof"F(s(x))"))
      b ((base, step) => {
        InductionRule(
          InductionCase(base, hoc"0:nat", Nil, Nil, Suc(0)) ::
            InductionCase(step, hoc"s:nat>nat", Ant(0) :: Nil, hov"x:nat" :: Nil, Suc(1)) ::
            Nil,
          Abs(hov"x:nat", le"F(x)"),
          hov"x:nat"
        )
      })
      c OpenAssumption(("" -> hof"F(x)") +: Sequent())
      b (CutRule(_, _, hof"F(x)"))
      c OpenAssumption(("" -> hof"A") +: Sequent())
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Left.reduce(proof): @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(1 :: 0 :: Nil) must beAnInstanceOf[CutRule]
  }

  "right rank cut induction should reduce" in {
    implicit var context: Context = Context()
    context += InductiveType("nat", hoc"0: nat", hoc"s:nat>nat")
    context += hoc"F:nat>o"
    context += hoc"A:o"
    val proof = (ProofBuilder
      c OpenAssumption(Sequent() :+ ("" -> hof"A"))
      c LogicalAxiom(hof"F(0)")
      c LogicalAxiom(hof"A")
      u (WeakeningLeftRule(_, hof"F(x)"))
      u (WeakeningRightRule(_, hof"F(s(x))"))
      b ((base, step) => {
        InductionRule(
          InductionCase(base, hoc"0:nat", Nil, Nil, Suc(0)) ::
            InductionCase(step, hoc"s:nat>nat", Ant(0) :: Nil, hov"x:nat" :: Nil, Suc(1)) ::
            Nil,
          Abs(hov"x:nat", le"F(x)"),
          hov"x:nat"
        )
      })
      c OpenAssumption(("" -> hof"F(x)") +: Sequent())
      b (CutRule(_, _, hof"F(x)"))
      b (CutRule(_, _, hof"A")) qed)
    val Some(newProof) = StuckCutReduction.Right.reduce(proof): @unchecked
    newProof.endSequent must beMultiSetEqual(proof.endSequent)
    newProof.subProofAt(1 :: 0 :: Nil) must beAnInstanceOf[CutRule]
  }

  "cut should reduce over multiple stuck cuts 1" in {
    val proof = (ProofBuilder
      c OpenAssumption(hols":- e:E")
      c OpenAssumption(hols":- c:C")
      c OpenAssumption(hols":- a:A")
      c OpenAssumption(hols"a: A, c:C :- b:B, d:D")
      u (WeakeningLeftRule(_, hof"E"))
      b (CutRule(_, _, hof"A"))
      c OpenAssumption(hols"b: B :-")
      b (CutRule(_, _, hof"B"))
      b (CutRule(_, _, hof"C"))
      c OpenAssumption(hols"d:D :-")
      b (CutRule(_, _, hof"D"))
      b (CutRule(_, _, hof"E")) qed)
    val newProof = cutNormal(proof)
    proof.endSequent must beMultiSetEqual(newProof.endSequent)
    (proof.subProofs.filter(_.isInstanceOf[CutRule]).size >
      newProof.subProofs.filter(_.isInstanceOf[CutRule]).size) must_== true
  }

  "cut should reduce over multiple stuck cuts 2" in {
    val proof = (ProofBuilder
      c OpenAssumption(hols":- e:E")
      c OpenAssumption(hols":- c:C")
      c OpenAssumption(hols":- a:A")
      c OpenAssumption(hols"a: A, c:C, e:E :- b:B, d:D")
      u (WeakeningRightRule(_, hof"F"))
      b (CutRule(_, _, hof"A"))
      c OpenAssumption(hols"b: B :-")
      b (CutRule(_, _, hof"B"))
      b (CutRule(_, _, hof"C"))
      c OpenAssumption(hols"d:D :-")
      b (CutRule(_, _, hof"D"))
      b (CutRule(_, _, hof"E"))
      c OpenAssumption(hols"f:F :- x:X")
      b (CutRule(_, _, hof"F")) qed)
    val newProof = cutNormal(proof)
    proof.endSequent must beMultiSetEqual(newProof.endSequent)
    (proof.subProofs.filter(_.isInstanceOf[CutRule]).size >
      newProof.subProofs.filter(_.isInstanceOf[CutRule]).size) must_== true
  }
}
