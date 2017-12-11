package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._

/* This proof is not a s.i.p. because of the nested
 * inductions.
 */
object prop_22 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
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
      goal: ∀a ∀b ∀c max2(max2(a:Nat, b:Nat): Nat, c:Nat) = max2(a, max2(b, c))
    """

  val proof = Lemma( sequent ) {
    allR
    induction( hov"a:Nat" )
    // base case
    allR
    allR
    allL( "def_max2_1", le"b:Nat" )
    allL( "def_max2_1", le"max2(b:Nat,c:Nat):Nat" )
    eql( "def_max2_1_0", "goal" ).fromLeftToRight
    eql( "def_max2_1_1", "goal" ).fromLeftToRight
    refl
    // inductive case
    allR
    allR
    induction( hov"b:Nat" )
    allL( "def_max2_2", le"a_0:Nat" )
    allL( "def_max2_1", le"c:Nat" )
    eql( "def_max2_2_0", "goal" ).fromLeftToRight
    eql( "def_max2_1_0", "goal" ).fromLeftToRight
    refl

    allL( "def_max2_3", le"a_0:Nat", le"b_0:Nat" )
    eql( "def_max2_3_0", "goal" )
    induction( hov"c:Nat" )
    allL( "def_max2_2", le"max2(a_0:Nat, b_0:Nat):Nat" )
    eql( "def_max2_2_0", "goal" ).fromLeftToRight
    allL( "def_max2_2", le"b_0:Nat" )
    eql( "def_max2_2_1", "goal" ).fromLeftToRight
    eql( "def_max2_3_0", "goal" ).fromLeftToRight
    refl

    allL( "def_max2_3", le"b_0:Nat", le"c_0:Nat" )
    allL( "def_max2_3", le"a_0:Nat", le"max2(b_0:Nat,c_0:Nat):Nat" )
    eql( "def_max2_3_1", "goal" )
    eql( "def_max2_3_2", "goal" )
    allL( "def_max2_3", le"max2(a_0:Nat,b_0:Nat):Nat", le"c_0:Nat" )
    eql( "def_max2_3_3", "goal" )
    allL( "IHa_0", le"b_0:Nat", le"c_0:Nat" )
    eql( "IHa_0_0", "goal" ).fromLeftToRight
    refl
  }
}
