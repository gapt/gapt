package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.Context
import gapt.proofs.gaptic._

object prop_30 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:Nat>list>list" )
  ctx += hoc"head:list>Nat"
  ctx += hoc"tail:list>list"

  ctx += hoc"'equal' :Nat>Nat>o"
  ctx += hoc"'elem' :Nat>list>o"
  ctx += hoc"'ins1' :Nat>list>list"
  ctx += hoc"'lt' :Nat>Nat>o"

  val sequent =
    hols"""
      def_p: ∀x p(S(x)) = x,
      def_head: ∀x0 ∀x1 (head(cons(x0:Nat, x1:list): list): Nat) = x0,
      def_tail: ∀x0 ∀x1 (tail(cons(x0:Nat, x1:list): list): list) = x1,
      def_lt_1: ∀x ¬lt(x:Nat, #c(Z: Nat)),
      def_lt_2: ∀z lt(#c(Z: Nat), S(z:Nat): Nat),
      def_lt_3: ∀x2 ∀z ((lt(S(x2:Nat): Nat, S(z)) → lt(x2, z)) ∧ (lt(x2, z) → lt(S(x2), S(z)))),
      def_ins_1: ∀x (ins(x:Nat, nil:list): list) = cons(x, nil),
      def_ins_2: ∀x ∀z ∀xs (¬lt(x:Nat, z:Nat) → (ins(x, cons(z, xs:list): list): list) = cons(z, ins(x, xs))),
      def_ins_3: ∀x ∀z ∀xs (lt(x:Nat, z:Nat) → (ins(x, cons(z, xs:list): list): list) = cons(x, cons(z, xs))),
      def_equal_1: equal(Z, Z),
      def_equal_2: ∀x ¬equal(Z, S(x)),
      def_equal_3: ∀x ¬equal(S(x), Z),
      def_equal_4: ∀x ∀y ((equal(S(x), S(y)) → equal(x, y)) ∧ (equal(x, y) → equal(S(x), S(y)))),
      def_elem_1: ∀x ¬elem(x:Nat, nil:list),
      def_elem_2: ∀x ∀z ∀xs ((elem(x:Nat, cons(z:Nat, xs:list): list) → equal(x, z) ∨ elem(x, xs)) ∧ (equal(x, z) ∨ elem(x, xs) → elem(x, cons(z, xs)))),
      ax_nat: ∀x ¬Z = S(x),
      ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
      :-
      goal: ∀x ∀xs elem(x:Nat, ins(x, xs:list): list)
    """

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
    // base case
    allL( "def_ins_1", le"x:Nat" )
    eql( "def_ins_1_0", "goal" )
    allL( "def_elem_2", le"x:Nat", le"x:Nat", le"nil:list" )
    andL
    impL( "def_elem_2_0_1" )
    orR
    induction( hov"x:Nat", "def_elem_2_0_1_0" )
    axiomLog
    allL( "def_equal_4", le"x_0:Nat", le"x_0:Nat" )
    andL
    impL( "def_equal_4_0_1" )
    axiomLog
    axiomLog
    axiomLog
    // inductive case
    allL( "def_ins_2", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    allL( "def_ins_3", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    impL( "def_ins_2_0" )
    negR
    impL( "def_ins_3_0" )
    axiomLog
    eql( "def_ins_3_0", "goal" )
    allL( "def_elem_2", le"x:Nat", le"x:Nat", le"cons(x_0:Nat, xs_0:list):list" )
    andL
    impL( "def_elem_2_0_1" )
    orR
    // proof of equal(x,x)
    induction( hov"x:Nat", "def_elem_2_0_1_0" )
    axiomLog
    allL( "def_equal_4", le"x_1:Nat", le"x_1:Nat" )
    andL
    impL( "def_equal_4_0_1" )
    axiomLog
    axiomLog

    axiomLog
    eql( "def_ins_2_0", "goal" )
    allL( "def_elem_2", le"x:Nat", le"x_0:Nat", le"ins(x:Nat, xs_0:list):list" )
    andL
    impL( "def_elem_2_0_1" )
    orR
    axiomLog
    axiomLog
  }
}
