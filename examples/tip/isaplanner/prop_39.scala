package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.gaptic._
import gapt.proofs.{ Context, Sequent }

object prop_39 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:Nat>list>list" )
  ctx += hoc"head:list>Nat"
  ctx += hoc"tail:list>list"

  ctx += hoc"'equal' :Nat>Nat>o"
  ctx += hoc"'count' :Nat>list>Nat"
  ctx += hoc"'plus' :Nat>Nat>Nat"

  val sequent =
    hols"""
          def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
          def_head: ∀x0 ∀x1 (head(cons(x0:Nat, x1:list): list): Nat) = x0,
          def_tail: ∀x0 ∀x1 (tail(cons(x0:Nat, x1:list): list): list) = x1,
          def_plus_1: ∀y (plus(#c(Z: Nat), y:Nat): Nat) = y,
          def_plus_2: ∀z ∀y (plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y)),
          def_equal_1: equal(#c(Z: Nat), #c(Z: Nat)): o,
          def_equal_2: ∀z ¬equal(#c(Z: Nat), S(z:Nat): Nat),
          def_equal_3: ∀x2 ¬equal(S(x2:Nat): Nat, #c(Z: Nat)),
          def_equal_4: ∀x2 ∀y2 ((equal(S(x2:Nat): Nat, S(y2)) → equal(x2, y2)) ∧ (equal(x2, y2) → equal(S(x2), S(y2)))),
          def_count_1: ∀x (count(x:Nat, nil:list): Nat) = #c(Z: Nat),
          def_count_2: ∀x ∀z ∀ys (¬equal(x:Nat, z:Nat) → (count(x, cons(z, ys:list): list): Nat) = count(x, ys)),
          def_count_3: ∀x ∀z ∀ys (equal(x:Nat, z:Nat) → (count(x, cons(z, ys:list): list): Nat) = S(count(x, ys))),
          ax_nat: ∀y0 ¬#c(Z: Nat) = S(y0:Nat),
          ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
          :-
          goal: ∀n ∀x ∀xs (plus(count(n:Nat, cons(x:Nat, nil:list): list): Nat, count(n, xs)): Nat) = count(n, cons(x, xs))
        """

  val cutFormula = hof"∀xs ∀n ∀x plus(count(n, cons(x, nil)), count(n, xs)) = count(n, cons(x, xs))"

  val proofCF = Lemma(
    sequent.antecedent ++: Sequent() :+ ( "c" -> cutFormula ) ) {
      allR
      induction( on = hov"xs:list" )
      allR
      allR
      // base case
      allL( "def_count_1", le"n:Nat" )
      eql( "def_count_1_0", "c" )
      allL( "def_count_2", le"n:Nat", le"x:Nat", le"nil:list" )
      allL( "def_count_3", le"n:Nat", le"x:Nat", le"nil:list" )
      impL( "def_count_2_0" )
      negR
      impL( "def_count_3_0" )
      axiomLog
      eql( "def_count_3_0", "c" )
      eql( "def_count_1_0", "c" ).fromLeftToRight
      allL( "def_plus_2", le"Z:Nat", le"Z:Nat" )
      allL( "def_plus_1", le"Z:Nat" )
      eql( "def_plus_2_0", "c" )
      eql( "def_plus_1_0", "c" ).fromLeftToRight
      refl
      allL( "def_plus_1", le"Z:Nat" )
      eql( "def_count_2_0", "c" )
      eql( "def_count_1_0", "c" ).fromLeftToRight
      axiomLog
      // inductive case
      allR
      allR
      allL( "def_count_1", le"n:Nat" )
      allL( "def_count_2", le"n:Nat", le"x:Nat", le"xs_0:list" )
      allL( "def_count_3", le"n:Nat", le"x:Nat", le"xs_0:list" )
      impL( "def_count_2_0" )
      negR
      impL( "def_count_3_0" )
      axiomLog
      eql( "def_count_3_0", "c" )
      allL( "def_count_2", le"n:Nat", le"x_0:Nat", le"nil:list" )
      allL( "def_count_3", le"n:Nat", le"x_0:Nat", le"nil:list" )
      impL( "def_count_2_1" )
      negR
      impL( "def_count_3_1" )
      axiomLog
      eql( "def_count_3_1", "c" )
      allL( "def_count_3", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      impL( "def_count_3_2" )
      axiomLog
      eql( "def_count_3_2", "c" )
      allL( "def_plus_2", le"Z:Nat", le"S(count(n:Nat,xs_0:list))" )
      allL( "def_plus_1", le"S(count(n:Nat,xs_0:list))" )
      eql( "def_count_1_0", "c" )
      eql( "def_plus_2_0", "c" )
      eql( "def_plus_1_0", "c" ).fromLeftToRight
      eql( "def_count_3_0", "c" ).fromLeftToRight
      refl
      allL( "def_plus_1", le"S(count(n:Nat,xs_0:list))" )
      allL( "def_count_2", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      allL( "def_count_3", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      impL( "def_count_2_2" )
      negR
      impL( "def_count_3_2" )
      axiomLog
      eql( "def_count_3_2", "c" )
      eql( "def_count_3_0", "c" ).fromLeftToRight
      allL( "def_count_3", le"n:Nat", le"x_0:Nat", le"nil:list" )
      impL( "def_count_3_3" )
      axiomLog
      eql( "def_count_3_3", "c" )
      eql( "def_count_1_0", "c" )
      allL( "def_plus_2", le"Z:Nat", le"S(count(n:Nat,xs_0:list))" )
      eql( "def_plus_2_0", "c" )
      allL( "def_plus_1", le"S(count(n:Nat,xs_0:list))" )
      eql( "def_plus_1_1", "c" ).fromLeftToRight
      refl
      eql( "def_count_2_1", "c" )
      eql( "def_count_1_0", "c" )
      eql( "def_plus_1_0", "c" ).fromLeftToRight
      eql( "def_count_2_2", "c" )
      eql( "def_count_3_0", "c" ).fromLeftToRight
      refl
      eql( "def_count_2_0", "c" )
      allL( "def_count_2", le"n:Nat", le"x_0:Nat", le"nil:list" )
      allL( "def_count_3", le"n:Nat", le"x_0:Nat", le"nil:list" )
      impL( "def_count_2_1" )
      negR
      impL( "def_count_3_1" )
      axiomLog
      eql( "def_count_3_1", "c" )
      eql( "def_count_1_0", "c" )
      allL( "def_count_3", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      impL( "def_count_3_2" )
      axiomLog
      eql( "def_count_3_2", "c" )
      allL( "def_plus_2", le"Z:Nat", le"count(n:Nat,xs_0:list)" )
      allL( "def_plus_1", le"count(n:Nat,xs_0:list)" )
      eql( "def_plus_2_0", "c" )
      eql( "def_plus_1_0", "c" ).fromLeftToRight
      eql( "def_count_2_0", "c" ).fromLeftToRight
      refl
      allL( "def_count_2", le"n:Nat", le"x_0:Nat", le"cons(x:Nat, xs_0:list)" )
      allL( "def_count_3", le"n:Nat", le"x_0:Nat", le"cons(x:Nat, xs_0:list)" )
      impL( "def_count_3_2" )
      impL( "def_count_2_2" )
      negR
      axiomLog
      allL( "def_plus_1", le"count(n:Nat,xs_0:list)" )
      eql( "def_count_2_2", "c" )
      eql( "def_count_2_1", "c" )
      eql( "def_count_1_0", "c" )
      eql( "def_plus_1_0", "c" ).fromLeftToRight
      eql( "def_count_2_0", "c" ).fromLeftToRight
      refl
      allL( "def_count_2", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      allL( "def_count_3", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      impL( "def_count_2_3" )
      negR
      impL( "def_count_3_3" )
      axiomLog
      allL( "def_plus_2", le"Z:Nat", le"count(n:Nat,xs_0:list)" )
      allL( "def_plus_1", le"count(n:Nat,xs_0:list)" )
      eql( "def_count_3_2", "c" )
      impL( "def_count_3_1" )
      axiomLog
      allL( "def_plus_2", le"Z:Nat", le"count(n:Nat,xs_0:list)" )
      allL( "def_plus_1", le"count(n:Nat,xs_0:list)" )
      eql( "def_count_3_1", "c" )
      eql( "def_count_1_0", "c" )
      eql( "def_plus_2_0", "c" )
      eql( "def_plus_1_0", "c" ).fromLeftToRight
      eql( "def_count_2_0", "c" ).fromLeftToRight
      refl
      allL( "def_plus_1", le"count(n:Nat,xs_0:list)" )
      eql( "def_count_2_3", "c" )
      eql( "def_count_2_1", "c" )
      eql( "def_count_1_0", "c" )
      eql( "def_plus_1_0", "c" ).fromLeftToRight
      eql( "def_count_2_0", "c" ).fromLeftToRight
      refl
    }

  val proof = Lemma( sequent ) {
    cut( "c", cutFormula )
    insert( proofCF )
    allR
    allR
    allR
    allL( "c", le"xs:list", le"n:Nat", le"x:Nat" )
    axiomLog
  }

}
