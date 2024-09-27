package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

object prop_37 extends TacticsProof {

  ctx += InductiveType(ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat")
  ctx += hoc"p:Nat>Nat"

  ctx += InductiveType(ty"list", hoc"nil:list", hoc"cons:Nat>list>list")
  ctx += hoc"head:list>Nat"
  ctx += hoc"tail:list>list"

  ctx += hoc"'equal' :Nat>Nat>o"
  ctx += hoc"'elem' :Nat>list>o"
  ctx += hoc"'delete' :Nat>list>list"

  val sequent =
    hols"""
          def_head: ∀x0 ∀x1 (head(cons(x0:Nat, x1:list): list): Nat) = x0,
          def_tail: ∀x0 ∀x1 (tail(cons(x0:Nat, x1:list): list): list) = x1,
          def_equal_1: equal(#c(Z: Nat), #c(Z: Nat)): o,
          def_equal_2: ∀z ¬equal(#c(Z: Nat), S(z:Nat): Nat),
          def_equal_3: ∀x2 ¬equal(S(x2:Nat): Nat, #c(Z: Nat)),
          def_equal_4: ∀x2 ∀y2 ((equal(S(x2:Nat): Nat, S(y2)) → equal(x2, y2)) ∧ (equal(x2, y2) → equal(S(x2), S(y2)))),
          def_elem_1: ∀x ¬elem(x:Nat, nil:list),
          def_elem_2: ∀x ∀z ∀xs ((elem(x:Nat, cons(z:Nat, xs:list): list) → equal(x, z) ∨ elem(x, xs)) ∧ (equal(x, z) ∨ elem(x, xs) → elem(x, cons(z, xs)))),
          def_delete_1: ∀x (delete(x:Nat, nil:list): list) = nil,
          def_delete_2: ∀x ∀z ∀xs (¬equal(x:Nat, z:Nat) → (delete(x, cons(z, xs:list): list): list) = cons(z, delete(x, xs))),
          def_delete_3: ∀x ∀z ∀xs (equal(x:Nat, z:Nat) → (delete(x, cons(z, xs:list): list): list) = delete(x, xs)),
          ax_nat: ∀y0 ¬#c(Z: Nat) = S(y0:Nat),
          ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
          :-
          goal: ∀x ∀xs ¬elem(x:Nat, delete(x, xs:list): list)
        """

  val proof = Lemma(sequent) {
    allR
    allR
    induction(hov"xs:list")
    // base case
    allL("def_delete_1", le"x:Nat")
    allL("def_elem_1", le"x:Nat")
    eql("def_delete_1_0", "goal").fromLeftToRight
    axiomLog
    // inductive case
    decompose
    allL("def_delete_2", le"x:Nat", le"x_0:Nat", le"xs_0:list")
    impL
    negR
    allL("def_delete_3", le"x:Nat", le"x_0:Nat", le"xs_0:list")
    impL
    axiomLog
    eql("def_delete_3_0", "goal")
    axiomLog
    allL("def_elem_2", le"x:Nat", le"x_0:Nat", le"delete(x:Nat,xs_0:list)")
    andL
    impL("def_elem_2_0_0")
    eql("def_delete_2_0", "goal")
    axiomLog
    orL
    allL("def_delete_3", le"x:Nat", le"x_0:Nat", le"xs_0:list")
    impL("def_delete_3_0")
    axiomLog
    eql("def_delete_3_0", "goal")
    axiomLog
    axiomLog
  }
}
