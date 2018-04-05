package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.Context
import gapt.proofs.gaptic._

object prop_14 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += TBase( "fun1" )

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:sk>list>list" )
  ctx += hoc"head:list>sk"
  ctx += hoc"tail:list>list"

  ctx += hoc"'filter' :fun1>list>list"
  ctx += hoc"'append' :list>list>list"

  val sequent = hols"""
                      def_head: ∀x ∀xs head(cons(x, xs)) = x,
                      def_tail: ∀x ∀xs tail(cons(x, xs)) = xs,
                      def_filter_1: ∀x (filter(x:fun1, nil:list): list) = nil,
                      def_filter_2: ∀x ∀z ∀xs (¬apply1(x:fun1, z:sk) → (filter(x, cons(z, xs:list): list): list) = filter(x, xs)),
                      def_filter_3: ∀x ∀z ∀xs (apply1(x:fun1, z:sk) → (filter(x, cons(z, xs:list): list): list) = cons(z, filter(x, xs))),
                      def_append_1: ∀y (append(nil:list, y:list): list) = y,
                      def_append_2: ∀z ∀xs ∀y (append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y)),
                      ax_list: ∀x ∀xs ¬nil = cons(x, xs)
                      :-
                      goal: ∀p ∀xs ∀ys (filter(p:fun1, append(xs:list, ys:list): list): list) = append(filter(p, xs), filter(p, ys))
    """

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
    // base case
    allR
    allL( "def_filter_1", le"p:fun1" )
    allL( "def_append_1", le"ys:list" )
    allL( "def_append_1", le"filter(p:fun1, ys:list):list" )
    eql( "def_filter_1_0", "goal" ).fromLeftToRight
    eql( "def_append_1_0", "goal" ).fromLeftToRight
    eql( "def_append_1_1", "goal" ).fromLeftToRight
    refl
    // inductive case
    allR
    allL( "def_append_2", le"x:sk", le"xs_0:list", le"ys:list" )
    eql( "def_append_2_0", "goal" )
    allL( "def_filter_2", le"p:fun1", le"x:sk", le"append(xs_0:list, ys:list):list" )
    allL( "def_filter_3", le"p:fun1", le"x:sk", le"append(xs_0:list, ys:list):list" )
    impL( "def_filter_2_0" )
    negR
    impL( "def_filter_3_0" )
    axiomLog

    eql( "def_filter_3_0", "goal" )
    allL( "IHxs_0", le"ys:list" )
    eql( "IHxs_0_0", "goal" )
    allL( "def_filter_3", le"p:fun1", le"x:sk", le"xs_0:list" )
    impL( "def_filter_3_1" )
    axiomLog

    eql( "def_filter_3_1", "goal" )
    allL( "def_append_2", le"x:sk",
      le"filter(p:fun1, xs_0:list):list",
      le"filter(p:fun1, ys:list):list" )
    eql( "def_append_2_1", "goal" ).fromLeftToRight
    refl

    allL( "def_filter_2", le"p:fun1", le"x:sk", le"xs_0:list" )
    impL( "def_filter_2_1" )
    negR
    impL( "def_filter_3_0" )
    axiomLog

    allL( "def_filter_3", le"p:fun1", le"x:sk", le"xs_0:list" )
    impL( "def_filter_3_1" )
    axiomLog

    eql( "def_filter_3_1", "goal" )
    eql( "def_filter_3_0", "goal" )
    allL( "def_append_2", le"x:sk",
      le"filter(p:fun1, xs_0:list):list",
      le"filter(p:fun1, ys:list):list" )
    eql( "def_append_2_1", "goal" )
    allL( "IHxs_0", le"ys:list" )
    eql( "IHxs_0_0", "goal" ).fromLeftToRight
    refl

    eql( "def_filter_2_1", "goal" )
    eql( "def_filter_2_0", "goal" )
    allL( "IHxs_0", le"ys:list" )
    eql( "IHxs_0_0", "goal" ).fromLeftToRight
    refl
  }
}
