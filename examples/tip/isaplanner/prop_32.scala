package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

/* This proof is not a s.i.p. because of the subinductions. */
object prop_32 extends TacticsProof {

  ctx += TBase("sk")
  ctx += InductiveType(ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat")
  ctx += hoc"p:Nat>Nat"
  ctx += hoc"'min2' :Nat>Nat>Nat"

  val sequent =
    hols"""
      def_p: ∀x p(S(x)) = x,
      def_min2_1: ∀y (min2(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat),
      def_min2_2: ∀z (min2(S(z:Nat): Nat, #c(Z: Nat)): Nat) = #c(Z: Nat),
      def_min2_3: ∀z ∀y2 (min2(S(z:Nat): Nat, S(y2)): Nat) = S(min2(z, y2)),
      ax_nat: ∀x ¬Z = S(x)
      :-
      goal: ∀a ∀b (min2(a:Nat, b:Nat): Nat) = min2(b, a)
    """

  val proof = Lemma(sequent) {
    allR
    induction(hov"a:Nat")
    // base case
    allR
    allL("def_min2_1", le"b:Nat")
    eql("def_min2_1_0", "goal").fromLeftToRight
    induction(hov"b:Nat")
    allL("def_min2_1", le"Z:Nat")
    eql("def_min2_1_1", "goal").fromLeftToRight
    refl
    allL("def_min2_2", le"b_0:Nat")
    eql("def_min2_2_0", "goal").fromLeftToRight
    refl
    // inductive case
    allR
    induction(hov"b:Nat")
    allL("def_min2_1", le"S(a_0:Nat):Nat")
    allL("def_min2_2", le"a_0:Nat")
    eql("def_min2_1_0", "goal").fromLeftToRight
    eql("def_min2_2_0", "goal").fromLeftToRight
    refl
    allL("def_min2_3", le"a_0:Nat", le"b_0:Nat")
    allL("def_min2_3", le"b_0:Nat", le"a_0:Nat")
    allL("IHa_0", le"b_0:Nat")
    eql("def_min2_3_0", "goal")
    eql("def_min2_3_1", "goal")
    eql("IHa_0_0", "goal").fromRightToLeft
    refl
  }
}
