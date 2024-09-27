package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._
import gapt.provers.escargot.Escargot
import gapt.provers.viper.aip.axioms.IndependentInductionAxioms
import gapt.provers.viper.aip.axioms.SequentialInductionAxioms
import gapt.provers.viper.aip.AnalyticInductionProver
import gapt.provers.viper.aip.ProverOptions

object prop_10 extends TacticsProof {

  ctx += InductiveType(ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat")
  ctx += hoc"p:Nat>Nat"
  ctx += hoc"plus:Nat>Nat>Nat"
  ctx += hoc"minus:Nat>Nat>Nat"

  val sequent = hols"""
                          def_p: ∀x p(S(x)) = x,
                          def_minus_1: ∀x minus(Z, x) = Z,
                          def_minus_2: ∀x minus(S(x), Z) = S(x),
                          def_minus_3: ∀x ∀y minus(S(x), S(y)) = minus(x, y),
                          ax_nat_1: ∀x ¬Z = S(x)
                          :-
                          goal: ∀m minus(m, m) = Z
    """

  val proof = Lemma(sequent) {
    allR
    induction(hov"m:Nat")
    // base case
    allL("def_minus_1", le"Z:Nat")
    forget("def_p", "def_minus_1", "def_minus_2", "def_minus_3", "ax_nat_1")
    axiomLog

    // Inductive case
    allL("def_minus_3", le"m_0:Nat", le"m_0:Nat")
    forget("def_p", "def_minus_1", "def_minus_2", "def_minus_3", "ax_nat_1")
    eql("def_minus_3_0", "goal")
    axiomLog
  }

  val aipOptions1 = new ProverOptions(Escargot, IndependentInductionAxioms().forVariables(List(hov"m:Nat")).forLabel("goal"))
  val proof2 = new AnalyticInductionProver(aipOptions1) lkProof (sequent) get

  val aipOptions2 = new ProverOptions(Escargot, SequentialInductionAxioms().forVariables(List(hov"m:Nat")).forLabel("goal"))
  val proof3 = new AnalyticInductionProver(aipOptions2) lkProof (sequent) get

  val proof4 = Lemma(sequent) {
    treeGrammarInduction
      .useInterpolation
  }
}
