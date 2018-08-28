package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.context.Context
import gapt.proofs.gaptic._

object prop_15 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:Nat>list>list" )
  ctx += hoc"head:list>Nat"
  ctx += hoc"tail:list>list"

  ctx += hoc"lt:Nat>Nat>o"
  ctx += hoc"len:list>Nat"
  ctx += hoc"ins:Nat>list>list"

  val sequent = hols"""
                       def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
                       def_head: ∀x0 ∀x1 (head(cons(x0:Nat, x1:list): list): Nat) = x0,
                       def_tail: ∀x0 ∀x1 (tail(cons(x0:Nat, x1:list): list): list) = x1,
                       def_lt_1: ∀x ¬lt(x:Nat, #c(Z: Nat)),
                       def_lt_2: ∀z lt(#c(Z: Nat), S(z:Nat): Nat),
                       def_lt_3: ∀x2 ∀z ((lt(S(x2:Nat): Nat, S(z)) → lt(x2, z)) ∧ (lt(x2, z) → lt(S(x2), S(z)))),
                       def_len_1: (len(nil:list): Nat) = #c(Z: Nat),
                       def_len_2: ∀y ∀xs (len(cons(y:Nat, xs:list): list): Nat) = S(len(xs)),
                       def_ins_1: ∀x (ins(x:Nat, nil:list): list) = cons(x, nil),
                       def_ins_2: ∀x ∀z ∀xs (¬lt(x:Nat, z:Nat) → (ins(x, cons(z, xs:list): list): list) = cons(z, ins(x, xs))),
                       def_ins_3:∀x ∀z ∀xs (lt(x:Nat, z:Nat) → (ins(x, cons(z, xs:list): list): list) = cons(x, cons(z, xs))),
                       ax_nat_1:∀y0 ¬#c(Z: Nat) = S(y0:Nat),
                       ax_list_1:∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
                       :-
                       goal: ∀x ∀xs (len(ins(x:Nat, xs:list): list): Nat) = S(len(xs))
    """

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
    // base case
    allL( "def_ins_1", le"x:Nat" )
    allL( "def_len_2", le"x:Nat", le"nil:list" )
    eql( "def_ins_1_0", "goal" )
    eql( "def_len_2_0", "goal" ).fromLeftToRight
    refl
    // inductive case
    allL( "def_len_2", le"x_0:Nat", le"xs_0:list" )
    allL( "def_ins_2", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    allL( "def_ins_3", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    eql( "def_len_2_0", "goal" )
    impL( "def_ins_2_0" )
    negR
    impL( "def_ins_3_0" )
    axiomLog

    eql( "def_ins_3_0", "goal" )
    allL( "def_len_2", le"x:Nat", le"cons(x_0:Nat,xs_0:list)" )
    eql( "def_len_2_1", "goal" )
    eql( "def_len_2_0", "goal" ).fromLeftToRight
    refl

    eql( "def_ins_2_0", "goal" )
    allL( "def_len_2", le"x_0:Nat", le"ins(x:Nat, xs_0:list):list" )
    eql( "def_len_2_1", "goal" )
    eql( "IHxs_0", "goal" ).fromLeftToRight
    refl
  }

  val openind = proof
}
