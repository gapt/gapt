package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.context.Context
import gapt.proofs.gaptic._

/* This is not a s.i.p because of the nested induction which is
 * required to prove equal(x,x).
 */
object prop_29 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:Nat>list>list" )
  ctx += hoc"head:list>Nat"
  ctx += hoc"tail:list>list"

  ctx += hoc"'equal' :Nat>Nat>o"
  ctx += hoc"'elem' :Nat>list>o"
  ctx += hoc"'ins1' :Nat>list>list"

  val sequent =
    hols"""
      def_p: ∀x p(S(x)) = x,
      def_head: ∀x0 ∀x1 (head(cons(x0:Nat, x1:list): list): Nat) = x0,
      def_tail: ∀x0 ∀x1 (tail(cons(x0:Nat, x1:list): list): list) = x1,
      def_equal_1: equal(Z, Z),
      def_equal_2: ∀x ¬equal(Z, S(x)),
      def_equal_3: ∀x ¬equal(S(x), Z),
      def_equal_4: ∀x ∀y ((equal(S(x), S(y)) → equal(x, y)) ∧ (equal(x, y) → equal(S(x), S(y)))),
      def_ins_1: ∀x (ins1(x:Nat, nil:list): list) = cons(x, nil),
      def_ins_2: ∀x ∀z ∀xs (¬equal(x:Nat, z:Nat) → (ins1(x, cons(z, xs:list): list): list) = cons(z, ins1(x, xs))),
      def_ins_3: ∀x ∀z ∀xs (equal(x:Nat, z:Nat) → (ins1(x, cons(z, xs:list): list): list) = cons(z, xs)),
      def_elem_1: ∀x ¬elem(x:Nat, nil:list),
      def_elem_2: ∀x ∀z ∀xs ((elem(x:Nat, cons(z:Nat, xs:list): list) → equal(x, z) ∨ elem(x, xs)) ∧ (equal(x, z) ∨ elem(x, xs) → elem(x, cons(z, xs)))),
      ax_nat: ∀x ¬Z = S(x),
      ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
      :-
      goal: ∀x ∀xs elem(x:Nat, ins1(x, xs:list): list)
    """

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
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
    allL( "def_ins_2", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    impL
    negR
    allL( "def_ins_3", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    impL
    axiomLog
    eql( "def_ins_3_0", "goal" ).fromLeftToRight
    allL( "def_elem_2", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    andL
    impL( "def_elem_2_0_1" )
    orR
    axiomLog
    axiomLog
    eql( "def_ins_2_0", "goal" )
    allL( "def_elem_2", le"x:Nat", le"x_0:Nat", le"ins1(x:Nat, xs_0:list):list" )
    andL
    impL( "def_elem_2_0_1" )
    orR
    axiomLog
    axiomLog
  }
}
