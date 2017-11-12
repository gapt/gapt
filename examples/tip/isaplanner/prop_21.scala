package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._

object prop_21 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"
  ctx += hoc"'plus' :Nat>Nat>Nat"
  ctx += hoc"'le' :Nat>Nat>o"

  val sequent =
    hols"""
      def_p: ∀x p(S(x)) = x,
      def_plus_1: ∀y (plus(#c(Z: Nat), y:Nat): Nat) = y,
      def_plus_2: ∀z ∀y (plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y)),
      def_le_1: ∀y le(#c(Z: Nat), y:Nat),
      def_le_2: ∀z ¬le(S(z:Nat): Nat, #c(Z: Nat)),
      def_le_3: ∀z ∀x2 ((le(S(z:Nat): Nat, S(x2)) ⊃ le(z, x2)) ∧ (le(z, x2) ⊃ le(S(z), S(x2)))),
      ax_nat: ∀x ¬Z = S(x)
      :-
      goal: ∀n ∀m le(n:Nat, plus(n, m:Nat): Nat)
    """

  val proof = Lemma( sequent ) {
    allR
    induction( hov"n:Nat" )
    // base case
    allR
    allL( "def_le_1", le"plus(Z:Nat, m:Nat):Nat" )
    axiomLog
    // inductive case
    allR
    allL( "def_plus_2", le"n_0:Nat", le"m:Nat" )
    eql( "def_plus_2_0", "goal" )
    allL( "def_le_3", le"n_0:Nat", le"plus(n_0:Nat,m:Nat):Nat" )
    andL
    impL( "def_le_3_0_1" )
    allL( "IHn_0", le"m:Nat" )
    axiomLog

    axiomLog
  }
}
