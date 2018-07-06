package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.Context
import gapt.proofs.gaptic._

object prop_17 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"
  ctx += hoc"'le' :Nat>Nat>o"
  ctx += hoc"'equal' :Nat>Nat>o"

  val sequent =
    hols"""
          def_p: ∀x p(S(x)) = x,
          def_le_1: ∀x le(Z, x),
          def_le_2: ∀x ¬le(S(x), Z),
          def_le_3: ∀x ∀y (le(S(x), S(y)) ↔ le(x, y)),
          def_equal_1: equal(Z, Z),
          def_equal_2: ∀x ¬equal(Z, S(x)),
          def_equal_3: ∀x ¬equal(S(x), Z),
          def_equal_4: ∀x ∀y (equal(S(x), S(y)) ↔ equal(x, y)),
          ax_nat: ∀x ¬Z = S(x)
          :-
          goal: ∀n (le(n, Z) ↔ equal(n, Z))
        """

  val proof = Lemma( sequent ) {
    allR
    induction( hov"n:Nat" )
    by { // base case
      allL( "def_le_1", le"Z:Nat" )
      forget( "def_p", "def_le_1", "def_le_2", "def_le_3", "def_equal_2", "def_equal_3", "def_equal_4", "ax_nat" )
      andR
      impR
      axiomLog

      impR
      axiomLog
    }
    by { // inductive case
      allL( "def_le_2", le"n_0:Nat" )
      allL( "def_equal_3", le"n_0:Nat" )
      forget( "def_p", "def_le_1", "def_le_2", "def_le_3", "def_equal_2", "def_equal_3", "def_equal_4", "ax_nat" )
      andR
      impR
      negL( "def_le_2_0" )
      axiomLog

      impR
      negL( "def_equal_3_0" )
      axiomLog
    }
  }
}
