package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

/* This proof is not a s.i.p. */
object prop_23 extends TacticsProof {

  ctx += TBase("sk")
  ctx += InductiveType(ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat")
  ctx += hoc"p:Nat>Nat"
  ctx += hoc"'max2' :Nat>Nat>Nat"

  val sequent =
    hols"""
      def_p: ∀x p(S(x)) = x,
      def_max2_1: ∀y (max2(#c(Z: Nat), y:Nat): Nat) = y,
      def_max2_2: ∀z (max2(S(z:Nat): Nat, #c(Z: Nat)): Nat) = S(z),
      def_max2_3: ∀z ∀x2 (max2(S(z:Nat): Nat, S(x2)): Nat) = S(max2(z, x2)),
      ax_nat: ∀x ¬Z = S(x)
      :-
      goal: ∀a ∀b (max2(a:Nat, b:Nat): Nat) = max2(b, a)
    """

  val proof = Lemma(sequent) {
    allR
    induction(hov"a:Nat")
    allR
    allL("def_max2_1", le"b:Nat")
    eql("def_max2_1_0", "goal").fromLeftToRight
    induction(hov"b:Nat")
    allL("def_max2_1", le"Z:Nat")
    eql("def_max2_1_1", "goal").fromLeftToRight
    refl
    allL("def_max2_2", le"b_0:Nat")
    eql("def_max2_2_0", "goal").fromLeftToRight
    refl
    allR
    induction(hov"b:Nat")
    allL("def_max2_1", le"S(a_0:Nat):Nat")
    allL("def_max2_2", le"a_0:Nat")
    eql("def_max2_2_0", "goal").fromLeftToRight
    eql("def_max2_1_0", "goal").fromLeftToRight
    refl
    allL("def_max2_3", le"a_0:Nat", le"b_0:Nat")
    allL("def_max2_3", le"b_0:Nat", le"a_0:Nat")
    allL("IHa_0", le"b_0:Nat")
    eql("def_max2_3_0", "goal")
    eql("def_max2_3_1", "goal")
    eql("IHa_0_0", "goal").fromLeftToRight
    refl

  }
}
