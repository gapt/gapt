package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.context.Context
import gapt.proofs.gaptic._
import gapt.proofs.{ Sequent }

/* This proof is not a s.i.p. because of the subinduction on xs */
object prop_41 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += TBase( "fun1" )

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:sk>list>list" )
  ctx += hoc"head:list>sk"
  ctx += hoc"tail:list>list"

  ctx += hoc"'apply1' :fun1>sk>sk"
  ctx += hoc"'take' :Nat>list>list"
  ctx += hoc"'map2' :fun1>list>list"

  val sequent =
    hols"""
           def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
           def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
           def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
           def_take_1: ∀y (take(#c(Z: Nat), y:list): list) = nil,
           def_take_2: ∀z (take(S(z:Nat): Nat, nil:list): list) = nil,
           def_take_3: ∀z ∀x2 ∀x3 (take(S(z:Nat): Nat, cons(x2:sk, x3:list): list): list) = cons(x2, take(z, x3)),
           def_map2_1: ∀x (map2(x:fun1, nil:list): list) = nil,
           def_map2_2: ∀x ∀z ∀xs (map2(x:fun1, cons(z:sk, xs:list): list): list) = cons(apply1(x, z), map2(x, xs)),
           ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
           ax_nat: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
           :-
           goal: ∀n ∀f ∀xs (take(n:Nat, map2(f:fun1, xs:list): list): list) = map2(f, take(n, xs))
      """

  val cutFormula = hof"∀n ∀xs ∀f take(n, map2(f, xs)) = map2(f, take(n, xs))"

  val proofCF = Lemma( sequent.antecedent ++: Sequent() :+ ( "c" -> cutFormula ) ) {
    allR
    induction( on = hov"n:Nat" )
    allR
    allR
    allL( "def_take_1", le"xs:list" )
    allL( "def_take_1", le"map2(f,xs:list)" )
    allL( "def_map2_1", le"f:fun1" )
    eql( "def_take_1_0", "c" )
    eql( "def_take_1_1", "c" ).fromLeftToRight
    eql( "def_map2_1_0", "c" ).fromLeftToRight
    refl
    allR
    induction( on = hov"xs:list" )
    allR
    allL( "def_map2_1", le"f:fun1" )
    allL( "def_take_2", le"n_0:Nat" )
    eql( "def_take_2_0", "c" ).fromLeftToRight
    eql( "def_map2_1_0", "c" ).fromLeftToRight
    eql( "def_take_2_0", "c" ).fromLeftToRight
    refl
    allR
    allL( "def_map2_2", le"f:fun1", le"x:sk", le"xs_0:list" )
    allL( "def_map2_2", le"f:fun1", le"x:sk", le"take(n_0,xs_0)" )
    allL( "def_take_3", le"n_0:Nat", le"apply1(f,x:sk)", le"map2(f,xs_0:list)" )
    allL( "def_take_3", le"n_0:Nat", le"x:sk", le"xs_0:list" )
    allL( "IHn_0", le"xs_0:list", le"f:fun1" )
    eql( "def_map2_2_0", "c" )
    eql( "def_take_3_0", "c" )
    eql( "def_take_3_1", "c" )
    eql( "def_map2_2_1", "c" )
    eql( "IHn_0_0", "c" ).fromLeftToRight
    refl
  }

  val proof = Lemma( sequent ) {
    cut( "c", cutFormula )
    insert( proofCF )
    allR
    allR
    allR
    allL( "c", le"n:Nat", le"xs:list", le"f:fun1" )
    axiomLog
  }
}
