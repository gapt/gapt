package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.Context
import gapt.proofs.gaptic._

/* This proof is not a s.i.p. because of the subinduction required
 * to prove equal(n,n).
 */
object prop_38 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:Nat>list>list" )
  ctx += hoc"head:list>Nat"
  ctx += hoc"tail:list>list"

  ctx += hoc"'equal' :Nat>Nat>o"
  ctx += hoc"'count' :Nat>list>Nat"
  ctx += hoc"'append' :list>list>list"

  val sequent =
    hols"""
          def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
          def_head: ∀x0 ∀x1 (head(cons(x0:Nat, x1:list): list): Nat) = x0,
          def_tail: ∀x0 ∀x1 (tail(cons(x0:Nat, x1:list): list): list) = x1,
          def_equal_1: equal(#c(Z: Nat), #c(Z: Nat)): o,
          def_equal_2: ∀z ¬equal(#c(Z: Nat), S(z:Nat): Nat),
          def_equal_3: ∀x2 ¬equal(S(x2:Nat): Nat, #c(Z: Nat)),
          def_equal_4: ∀x2 ∀y2 ((equal(S(x2:Nat): Nat, S(y2)) → equal(x2, y2)) ∧ (equal(x2, y2) → equal(S(x2), S(y2)))),
          def_count_1: ∀x (count(x:Nat, nil:list): Nat) = #c(Z: Nat),
          def_count_2: ∀x ∀z ∀ys (¬equal(x:Nat, z:Nat) → (count(x, cons(z, ys:list): list): Nat) = count(x, ys)),
          def_count_3: ∀x ∀z ∀ys (equal(x:Nat, z:Nat) → (count(x, cons(z, ys:list): list): Nat) = S(count(x, ys))),
          def_append_1: ∀y (append(nil:list, y:list): list) = y,
          def_append_2: ∀z ∀xs ∀y (append(cons(z:Nat, xs:list): list, y:list): list) = cons(z, append(xs, y)),
          ax_nat: ∀y0 ¬#c(Z: Nat) = S(y0:Nat),
          ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
          :-
          goal: ∀n ∀xs (count(n:Nat, append(xs:list, cons(n, nil:list): list): list): Nat) = S(count(n, xs))
        """

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
    // base case
    allL( "def_append_1", le"cons(n:Nat,nil:list)" )
    allL( "def_count_1", le"n:Nat" )
    allL( "def_count_3", le"n:Nat", le"n:Nat", le"nil" )
    eql( "def_append_1_0", "goal" ).fromLeftToRight
    eql( "def_count_1_0", "goal" )
    impL( "def_count_3_0" )
    induction( hov"n:Nat", "def_count_3_0" )
    axiomLog
    allL( "def_equal_4", le"n_0:Nat", le"n_0:Nat" )
    andL
    impL( "def_equal_4_0_1" )
    axiomLog
    axiomLog
    eql( "def_count_3_0", "goal" )
    eql( "def_count_1_0", "goal" ).fromLeftToRight
    refl
    // inductive case
    allL( "def_append_2", le"x:Nat", le"xs_0:list", le"cons(n:Nat,nil:list)" )
    allL( "def_count_2", le"n:Nat", le"x:Nat", le"xs_0:list" )
    allL( "def_count_3", le"n:Nat", le"x:Nat", le"xs_0:list" )
    allL( "def_count_2", le"n:Nat", le"x:Nat", le"append(xs_0:list, cons(n:Nat,nil:list))" )
    allL( "def_count_3", le"n:Nat", le"x:Nat", le"append(xs_0:list, cons(n:Nat,nil:list))" )
    eql( "def_append_2_0", "goal" )
    impL( "def_count_3_0" )
    impL( "def_count_2_0" )
    negR
    axiomLog
    eql( "def_count_2_0", "goal" )
    impL( "def_count_2_1" )
    negR
    axiomLog
    eql( "def_count_2_1", "goal" )
    eql( "IHxs_0", "goal" ).fromLeftToRight
    refl
    impL( "def_count_3_1" )
    impL( "def_count_2_1" )
    negR
    axiomLog
    eql( "def_count_2_1", "goal" )
    impL( "def_count_2_0" )
    negR
    axiomLog
    eql( "def_count_2_0", "goal" )
    eql( "IHxs_0", "goal" ).fromLeftToRight
    refl
    eql( "def_count_3_1", "goal" )
    eql( "IHxs_0", "goal" )
    eql( "def_count_3_0", "goal" ).fromLeftToRight
    refl
  }
}
