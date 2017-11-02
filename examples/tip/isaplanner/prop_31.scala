package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._

object prop_31 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
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
      goal: ∀a ∀b ∀c min2(min2(a:Nat, b:Nat): Nat, c:Nat) = min2(a, min2(b, c))
    """

  val proof = Lemma( sequent ) {
    allR
    induction( hov"a:Nat" )
    // base case
    allR
    allR
    allL( "def_min2_1", le"b:Nat" )
    allL( "def_min2_1", le"min2(b:Nat,c:Nat):Nat" )
    allL( "def_min2_1", le"c:Nat" )
    eql( "def_min2_1_0", "goal" ).fromLeftToRight
    eql( "def_min2_1_1", "goal" ).fromLeftToRight
    eql( "def_min2_1_2", "goal" ).fromLeftToRight
    refl
    // inductive case
    allR
    induction( hov"b:Nat" )
    allR
    allL( "def_min2_2", le"a_0:Nat" )
    allL( "def_min2_1", le"c:Nat" )
    eql( "def_min2_1_0", "goal" ).fromLeftToRight
    eql( "def_min2_2_0", "goal" ).fromLeftToRight
    eql( "def_min2_1_0", "goal" ).fromLeftToRight
    refl
    allR
    allL( "def_min2_3", le"a_0:Nat", le"b_0:Nat" )
    eql( "def_min2_3_0", "goal" )
    induction( hov"c:Nat" )
    allL( "def_min2_2", le"b_0:Nat" )
    allL( "def_min2_2", le"a_0:Nat" )
    allL( "def_min2_2", le"min2(a_0, b_0)" )
    eql( "def_min2_2_0", "goal" ).fromLeftToRight
    eql( "def_min2_2_1", "goal" ).fromLeftToRight
    eql( "def_min2_2_2", "goal" ).fromLeftToRight
    refl
    allL( "def_min2_3", le"min2(a_0:Nat, b_0:Nat):Nat", le"c_0:Nat" )
    allL( "def_min2_3", le"b_0:Nat", le"c_0:Nat" )
    allL( "def_min2_3", le"a_0:Nat", le"min2(b_0:Nat, c_0:Nat):Nat" )
    allL( "IHa_0", le"b_0:Nat", le"c_0:Nat" )
    eql( "def_min2_3_1", "goal" )
    eql( "def_min2_3_2", "goal" )
    eql( "def_min2_3_3", "goal" )
    eql( "IHa_0_0", "goal" ).fromLeftToRight
    refl
  }
}
