package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._

object prop_27 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:Nat>list>list" )
  ctx += hoc"head:list>Nat"
  ctx += hoc"tail:list>list"

  ctx += hoc"'equal' :Nat>Nat>o"
  ctx += hoc"'elem' :Nat>list>o"
  ctx += hoc"'append' :list>list>list"

  val sequent =
    hols"""
      def_p: ∀x p(S(x)) = x,
      def_head: ∀x0 ∀x1 (head(cons(x0:Nat, x1:list): list): Nat) = x0,
      def_tail: ∀x0 ∀x1 (tail(cons(x0:Nat, x1:list): list): list) = x1,
      def_equal_1: equal(Z, Z),
      def_equal_2: ∀x ¬equal(Z, S(x)),
      def_equal_3: ∀x ¬equal(S(x), Z),
      def_equal_4: ∀x ∀y ((equal(S(x), S(y)) ⊃ equal(x, y)) ∧ (equal(x, y) ⊃ equal(S(x), S(y)))),
      def_elem_1: ∀x ¬elem(x:Nat, nil:list),
      def_elem_2: ∀x ∀z ∀xs ((elem(x:Nat, cons(z:Nat, xs:list): list) ⊃ equal(x, z) ∨ elem(x, xs)) ∧ (equal(x, z) ∨ elem(x, xs) ⊃ elem(x, cons(z, xs)))),
      def_append_1: ∀y (append(nil:list, y:list): list) = y,
      def_append_2: ∀z ∀xs ∀y (append(cons(z:Nat, xs:list): list, y:list): list) = cons(z, append(xs, y)) ,
      ax_nat: ∀x ¬Z = S(x),
      ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
      :-
      goal: ∀x ∀xs ∀ys (elem(x:Nat, ys:list) ⊃ elem(x, append(xs:list, ys)))
    """

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
    allR
    allL( "def_append_1", le"ys:list" )
    eql( "def_append_1_0", "goal" ).fromLeftToRight
    impR
    axiomLog
    allR
    allL( "def_append_2", le"x_0:Nat", le"xs_0:list", le"ys:list" )
    eql( "def_append_2_0", "goal" )
    allL( "def_elem_2", le"x:Nat", le"x_0:Nat", le"append(xs_0:list, ys:list):list" )
    andL( "def_elem_2_0" )
    impR
    impL( "def_elem_2_0_1" )
    orR
    allL( "IHxs_0", le"ys:list" )
    impL( "IHxs_0_0" )
    axiomLog
    axiomLog
    axiomLog
  }
}
