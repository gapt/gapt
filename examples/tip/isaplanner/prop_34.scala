package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

/* This proof is not a s.i.p. because of the subinductions. */
object prop_34 extends TacticsProof {

  ctx += TBase("sk")
  ctx += InductiveType(ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat")
  ctx += hoc"p:Nat>Nat"
  ctx += hoc"'min2' :Nat>Nat>Nat"
  ctx += hoc"'le' :Nat>Nat>o"
  ctx += hoc"'equal' :Nat>Nat>o"

  val sequent =
    hols"""
      def_p: ∀x p(S(x)) = x,
      def_min2_1: ∀y (min2(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat),
      def_min2_2: ∀z (min2(S(z:Nat): Nat, #c(Z: Nat)): Nat) = #c(Z: Nat),
      def_min2_3: ∀z ∀y2 (min2(S(z:Nat): Nat, S(y2)): Nat) = S(min2(z, y2)),
      def_le_1: ∀y le(#c(Z: Nat), y:Nat),
      def_le_2: ∀z ¬le(S(z:Nat): Nat, #c(Z: Nat)),
      def_le_3: ∀z ∀x2 ((le(S(z:Nat): Nat, S(x2)) → le(z, x2)) ∧ (le(z, x2) → le(S(z), S(x2)))),
      def_equal_1: equal(Z, Z),
      def_equal_2: ∀x ¬equal(Z, S(x)),
      def_equal_3: ∀x ¬equal(S(x), Z),
      def_equal_4: ∀x ∀y ((equal(S(x), S(y)) → equal(x, y)) ∧ (equal(x, y) → equal(S(x), S(y)))),
      ax_nat: ∀x ¬Z = S(x)
      :-
      goal: ∀a ∀b ((equal(min2(a:Nat, b:Nat): Nat, b) → le(b, a)) ∧ (le(b, a) → equal(min2(a, b), b)))
    """

  val proof = Lemma(sequent) {
    allR
    induction(hov"a:Nat")
    // base case
    allR
    allL("def_le_1", le"Z:Nat")
    andR
    induction(hov"b:Nat")
    impR
    axiomLog
    impR
    allL("def_min2_1", le"S(b_0:Nat):Nat")
    allL("def_equal_2", le"b_0:Nat")
    negL
    eql("def_min2_1_0", "goal_0").fromLeftToRight
    axiomLog
    induction(hov"b:Nat")
    impR
    allL("def_min2_1", le"Z:Nat")
    eql("def_min2_1_0", "goal_1").fromLeftToRight
    axiomLog
    allL("def_le_2", le"b_0:Nat")
    impR
    negL
    axiomLog
    // inductive case
    allR
    induction(hov"b:Nat")
    andR
    allL("def_le_1", le"S(a_0:Nat):Nat")
    impR
    axiomLog
    allL("def_min2_2", le"a_0:Nat")
    impR
    eql("def_min2_2_0", "goal_1").fromLeftToRight
    axiomLog
    andR
    allL("def_min2_3", le"a_0:Nat", le"b_0:Nat")
    allL("def_equal_4", le"min2(a_0:Nat,b_0:Nat):Nat", le"b_0:Nat")
    allL("def_le_3", le"b_0:Nat", le"a_0:Nat")
    allL("IHa_0", le"b_0:Nat")
    eql("def_min2_3_0", "goal")
    impR
    andL("def_equal_4_0")
    andL("def_le_3_0")
    andL("IHa_0_0")
    forget("IHa_0_0_1", "def_equal_4_0_1", "def_le_3_0_0")
    impL("def_equal_4_0_0")
    axiomLog
    impL("IHa_0_0_0")
    axiomLog
    impL("def_le_3_0_1")
    axiomLog
    axiomLog
    allL("def_le_3", le"b_0:Nat", le"a_0:Nat")
    allL("def_equal_4", le"min2(a_0:Nat, b_0:Nat):Nat", le"b_0:Nat")
    allL("IHa_0", le"b_0:Nat")
    allL("def_min2_3", le"a_0:Nat", le"b_0:Nat")
    andL("def_le_3_0")
    andL("def_equal_4_0")
    andL("IHa_0_0")
    forget("def_le_3_0_1", "IHa_0_0_0", "def_equal_4_0_0")
    eql("def_min2_3_0", "goal")
    impR
    impL("def_le_3_0_0")
    axiomLog
    impL("IHa_0_0_1")
    axiomLog
    impL("def_equal_4_0_1")
    axiomLog
    axiomLog
  }
}
