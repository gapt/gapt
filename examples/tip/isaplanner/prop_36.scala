package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._

object prop_36 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += TBase( "fun1" )

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:sk>list>list" )
  ctx += hoc"head:list>sk"
  ctx += hoc"tail:list>list"

  ctx += hoc"'takeWhile' :fun1>list>list"
  ctx += hoc"'apply1' :fun1>sk>o"
  ctx += hoc"'lam' :fun1"

  val sequent =
    hols"""
          def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
          def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
          def_takeWhile_1: ∀x (takeWhile(x:fun1, nil:list): list) = nil,
          def_takeWhile_2: ∀x ∀z ∀xs (¬apply1(x:fun1, z:sk) ⊃ (takeWhile(x, cons(z, xs:list): list): list) = nil),
          def_takeWhile_3: ∀x ∀z ∀xs (apply1(x:fun1, z:sk) ⊃ (takeWhile(x, cons(z, xs:list): list): list) = cons(z, takeWhile(x, xs))),
          ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
          def_apply1_1: ∀x ((apply1(lam:fun1, x:sk) ⊃ ⊤) ∧ (⊤ ⊃ apply1(lam, x)))
          :-
          goal: ∀xs (takeWhile(lam:fun1, xs:list): list) = xs
        """

  val proof = Lemma( sequent ) {
    allR
    induction( hov"xs:list" )
    // base case
    allL( "def_takeWhile_1", le"lam" )
    axiomLog
    // inductive case
    allL( "def_apply1_1", le"x:sk" )
    allL( "def_takeWhile_3", le"lam", le"x:sk", le"xs_0:list" )
    andL
    impL( "def_apply1_1_0_1" )
    forget( "goal" )
    prop // invoking axiomTop instead of prop throws an exception.
    impL( "def_takeWhile_3_0" )
    axiomLog
    eql( "def_takeWhile_3_0", "goal" )
    eql( "IHxs_0", "goal" ).fromLeftToRight
    refl
  }
}
