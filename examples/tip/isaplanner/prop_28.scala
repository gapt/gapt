package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.Context
import gapt.proofs.gaptic._

/* This is not a s.i.p because of the subinduction for equal(x,x). */
object prop_28 extends TacticsProof {

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
      def_equal_4: ∀x ∀y ((equal(S(x), S(y)) → equal(x, y)) ∧ (equal(x, y) → equal(S(x), S(y)))),
      def_elem_1: ∀x ¬elem(x:Nat, nil:list),
      def_elem_2: ∀x ∀z ∀xs ((elem(x:Nat, cons(z:Nat, xs:list): list) → equal(x, z) ∨ elem(x, xs)) ∧ (equal(x, z) ∨ elem(x, xs) → elem(x, cons(z, xs)))),
      def_append_1: ∀y (append(nil:list, y:list): list) = y,
      def_append_2: ∀z ∀xs ∀y (append(cons(z:Nat, xs:list): list, y:list): list) = cons(z, append(xs, y)) ,
      ax_nat: ∀x ¬Z = S(x),
      ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
      :-
      goal: ∀x ∀xs elem(x:Nat, append(xs:list, cons(x, nil:list): list): list)
    """

  val proof = Lemma( sequent ) {
    cut( "goal_c", hof"∀xs ∀x elem(x, append(xs, cons(x, nil)))" )
    forget( "goal" )
    allR
    induction( hov"xs:list" )
    allR
    allL( "def_append_1", le"cons(x:Nat, nil:list):list" )
    eql( "def_append_1_0", "goal_c" ).fromLeftToRight
    allL( "def_elem_2", le"x:Nat", le"x:Nat", le"nil:list" )
    andL
    impL( "def_elem_2_0_1" )
    orR
    induction( hov"x:Nat", "def_elem_2_0_1_0" )
    axiomLog
    allL( "def_equal_4", le"x_0:Nat", le"x_0:Nat" )
    andL( "def_equal_4_0" )
    impL( "def_equal_4_0_1" )
    axiomLog
    axiomLog
    axiomLog
    allR
    allL( "def_append_2", le"x:Nat", le"xs_0:list", le"cons(x_0:Nat, nil:list):list" )
    eql( "def_append_2_0", "goal_c" )
    allL( "def_elem_2", le"x_0:Nat", le"x:Nat", le"append(xs_0:list, cons(x_0:Nat, nil:list):list):list" )
    andL( "def_elem_2_0" )
    impL( "def_elem_2_0_1" )
    orR
    allL( "IHxs_0", le"x_0:Nat" )
    axiomLog
    axiomLog
    allR
    allR
    allL( "goal_c", le"xs:list", le"x:Nat" )
    axiomLog
  }
}
