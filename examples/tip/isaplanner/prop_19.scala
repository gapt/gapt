package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

/* This is not a s.i.p. because of the nested induction. */
object prop_19 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += InductiveType( ty"list", hoc"nil:list", hoc"cons:sk>list>list" )
  ctx += hoc"head:list>sk"
  ctx += hoc"tail:list>list"

  ctx += hoc"'minus' :Nat>Nat>Nat"
  ctx += hoc"'len' :list>Nat"
  ctx += hoc"'drop' :Nat>list>list"

  val sequent =
    hols"""
          def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
          def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
          def_p: ∀x p(S(x)) = x,
          def_minus_1: ∀y (minus(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat),
          def_minus_2: ∀z (minus(S(z:Nat): Nat, #c(Z: Nat)): Nat) = S(z),
          def_minus_3: ∀z ∀x2 (minus(S(z:Nat): Nat, S(x2)): Nat) = minus(z, x2),
          def_len_1: (len(nil:list): Nat) = #c(Z: Nat),
          def_len_2: ∀y ∀xs (len(cons(y:sk, xs:list): list): Nat) = S(len(xs)),
          def_drop_1: ∀y (drop(#c(Z: Nat), y:list): list) = y,
          def_drop_2: ∀z (drop(S(z:Nat): Nat, nil:list): list) = nil,
          def_drop_3: ∀z ∀x2 ∀x3 (drop(S(z:Nat): Nat, cons(x2:sk, x3:list): list): list) = drop(z, x3),
          ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
          ax_nat: ∀x ¬Z = S(x)
          :-
          goal: ∀n ∀xs (len(drop(n:Nat, xs:list): list): Nat) = minus(len(xs), n)
        """

  val proof = Lemma( sequent ) {
    allR
    induction( hov"n:Nat" )
    // base case
    allR
    allL( "def_drop_1", le"xs:list" )
    eql( "def_drop_1_0", "goal" ).fromLeftToRight
    induction( hov"xs:list" )
    allL( "def_minus_1", le"Z:Nat" )
    eql( "def_len_1", "goal" ).fromLeftToRight
    eql( "def_minus_1_0", "goal" ).fromLeftToRight
    refl

    allL( "def_len_2", le"x:sk", le"xs_0:list" )
    allL( "def_minus_2", le"len(xs_0:list):Nat" )
    eql( "def_len_2_0", "goal" )
    eql( "def_minus_2_0", "goal" ).fromLeftToRight
    refl

    // inductive case
    allR
    induction( hov"xs:list" )
    allL( "def_drop_2", le"n_0:Nat" )
    allL( "def_minus_1", le"S(n_0:Nat):Nat" )
    eql( "def_drop_2_0", "goal" ).fromLeftToRight
    eql( "def_len_1", "goal" ).fromLeftToRight
    eql( "def_minus_1_0", "goal" ).fromLeftToRight
    refl
    allL( "def_drop_3", le"n_0:Nat", le"x:sk", le"xs_0:list" )
    allL( "def_len_2", le"x:sk", le"xs_0:list" )
    allL( "def_minus_3", le"len(xs_0:list):Nat", le"n_0:Nat" )
    allL( "IHn_0", le"xs_0:list" )
    eql( "def_drop_3_0", "goal" )
    eql( "def_len_2_0", "goal" )
    eql( "def_minus_3_0", "goal" )
    axiomLog
  }
}
