package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

object prop_26 extends TacticsProof {

  ctx += InductiveType(ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat")
  ctx += hoc"p:Nat>Nat"

  ctx += InductiveType(ty"list", hoc"nil:list", hoc"cons:Nat>list>list")
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
      goal: ∀x ∀xs ∀ys (elem(x:Nat, xs:list) → elem(x, append(xs, ys:list)))
    """

  val proof = Lemma(sequent) {
    allR
    allR
    induction(hov"xs:list")
    // base case
    allR
    impR
    allL("def_elem_1", le"x:Nat")
    negL("def_elem_1_0")
    axiomLog
    allR
    impR
    allL("def_elem_2", le"x:Nat", le"x_0:Nat", le"xs_0:list")
    andL("def_elem_2_0")
    impL("def_elem_2_0_0")
    axiomLog
    orL("def_elem_2_0_0")
    allL("def_append_2", le"x_0:Nat", le"xs_0:list", le"ys:list")
    eql("def_append_2_0", "goal_1").fromLeftToRight

    allL("def_elem_2", le"x:Nat", le"x_0:Nat", le"append(xs_0:list, ys:list):list")
    andL("def_elem_2_1")
    impL("def_elem_2_1_1")
    orR("def_elem_2_1_1")
    axiomLog
    axiomLog

    allL("def_append_2", le"x_0:Nat", le"xs_0:list", le"ys:list")
    eql("def_append_2_0", "goal_1").fromLeftToRight
    allL("def_elem_2", le"x:Nat", le"x_0:Nat", le"append(xs_0:list, ys:list):list")
    andL("def_elem_2_1")
    impL("def_elem_2_1_1")
    orR("def_elem_2_1_1")
    allL("IHxs_0", le"ys:list")
    impL("IHxs_0_0")
    axiomLog
    axiomLog
    axiomLog
  }
}
