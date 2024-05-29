package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

object prop_18 extends TacticsProof {

  ctx += TBase("sk")
  ctx += InductiveType(ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat")
  ctx += hoc"p:Nat>Nat"
  ctx += hoc"'plus' :Nat>Nat>Nat"
  ctx += hoc"'lt' :Nat>Nat>o"

  val sequent =
    hols"""
          def_p: ∀x p(S(x)) = x,
          def_plus_1: ∀y (plus(#c(Z: Nat), y:Nat): Nat) = y,
          def_plus_2: ∀z ∀y (plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y)),
          def_lt_1: ∀x ¬lt(x:Nat, #c(Z: Nat)),
          def_lt_2: ∀z lt(#c(Z: Nat), S(z:Nat): Nat),
          def_lt_3: ∀x2 ∀z ((lt(S(x2:Nat): Nat, S(z)) → lt(x2, z)) ∧ (lt(x2, z) → lt(S(x2), S(z)))),
          ax_nat: ∀x ¬Z = S(x)
          :-
          goal: ∀i ∀m lt(i:Nat, S(plus(i, m:Nat): Nat): Nat)
        """

  val proof = Lemma(sequent) {
    allR
    induction(hov"i:Nat")
    // Base case
    allR
    allL("def_lt_2", le"plus(Z:Nat, m:Nat):Nat")
    axiomLog
    // Inductive case
    allR
    allL("IHi_0", le"m:Nat")
    allL("def_lt_3", le"i_0:Nat", le"plus(S(i_0:Nat):Nat, m:Nat)")
    andL
    impL("def_lt_3_0_1")
    allL("def_plus_2", le"i_0:Nat", le"m:Nat")
    eql("def_plus_2_0", "def_lt_3_0_1")
    axiomLog

    axiomLog
  }
}
