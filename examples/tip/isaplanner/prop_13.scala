package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.Context
import gapt.proofs.gaptic._

object prop_13 extends TacticsProof {

  ctx += TBase( "sk" )

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:sk>list>list" )
  ctx += hoc"head:list>sk"
  ctx += hoc"tail:list>list"

  ctx += hoc"'drop' :Nat>list>list"

  val sequent = hols"""
                      def_head: ∀x ∀xs head(cons(x, xs)) = x,
                      def_tail: ∀x ∀xs tail(cons(x, xs)) = xs,
                      def_p: ∀x p(S(x)) = x,
                      def_drop_1: ∀y (drop(#c(Z: Nat), y:list): list) = y,
                      def_drop_2: ∀z (drop(S(z:Nat): Nat, nil:list): list) = nil,
                      def_drop_3: ∀z ∀x2 ∀x3 (drop(S(z:Nat): Nat, cons(x2:sk, x3:list): list): list) = drop(z, x3),
                      ax_list: ∀x ∀xs ¬nil = cons(x, xs),
                      ax_nat: ∀x ¬Z = S(x)
                      :-
                      goal: ∀n ∀x ∀xs (drop(S(n:Nat): Nat, cons(x:sk, xs:list): list): list) = drop(n, xs)
    """

  val proof = Lemma( sequent ) {
    trivial
  }
}
