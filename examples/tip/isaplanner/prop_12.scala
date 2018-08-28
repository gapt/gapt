package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.context.Context
import gapt.proofs.gaptic._

object prop_12 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += TBase( "fun1" )

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:sk>list>list" )
  ctx += hoc"head:list>sk"
  ctx += hoc"tail:list>list"

  ctx += hoc"drop:Nat>list>list"
  ctx += hoc"'map2' :fun1>list>list"
  ctx += hoc"'apply1' :fun1>sk>sk"

  val sequent = hols"""
                      def_head: ∀x ∀xs head(cons(x, xs)) = x,
                      def_tail: ∀x ∀xs tail(cons(x, xs)) = xs,
                      def_p: ∀x p(S(x)) = x,
                      def_map2_1: ∀x (map2(x:fun1, nil:list): list) = nil,
                      def_map2_2: ∀x ∀z ∀xs (map2(x:fun1, cons(z:sk, xs:list): list): list) =   cons(apply1(x, z), map2(x, xs)),
                      def_drop_1: ∀y (drop(#c(Z: Nat), y:list): list) = y,
                      def_drop_2: ∀z (drop(S(z:Nat): Nat, nil:list): list) = nil,
                      def_drop_3: ∀z ∀x2 ∀x3 (drop(S(z:Nat): Nat, cons(x2:sk, x3:list): list): list) = drop(z, x3),
                      ax_list: ∀x ∀xs ¬nil = cons(x, xs),
                      ax_nat: ∀x ¬Z = S(x)
                      :-
                      goal: ∀n ∀f ∀xs (drop(n:Nat, map2(f:fun1, xs:list): list): list) = map2(f, drop(n, xs))
    """

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"n:Nat" )
    // Base case
    allR
    allL( "def_drop_1", le"map2(f,xs:list):list" )
    allL( "def_drop_1", le"xs:list" )
    eql( "def_drop_1_0", "goal" ).fromLeftToRight
    eql( "def_drop_1_1", "goal" ).fromLeftToRight
    refl
    // Step case
    allR
    induction( hov"xs:list" )
    /// Base case
    rewrite.many ltr "def_map2_1"
    rewrite.many ltr "def_drop_2"
    rewrite.many ltr "def_map2_1"
    refl
    /// Step case
    rewrite.many ltr "def_map2_2"
    rewrite.many ltr "def_drop_3"
    chain( "IHn_0" )
  }
}
