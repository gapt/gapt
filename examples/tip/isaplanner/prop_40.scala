package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

object prop_40 extends TacticsProof {

  ctx += TBase( "sk" )

  ctx += InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += InductiveType( ty"list", hoc"nil:list", hoc"cons:sk>list>list" )
  ctx += hoc"head:list>sk"
  ctx += hoc"tail:list>list"

  ctx += hoc"'take' :Nat>list>list"

  val sequent =
    hols"""
           def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
           def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
           def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
           def_take_1: ∀y (take(#c(Z: Nat), y:list): list) = nil,
           def_take_2: ∀z (take(S(z:Nat): Nat, nil:list): list) = nil,
           def_take_3: ∀z ∀x2 ∀x3 (take(S(z:Nat): Nat, cons(x2:sk, x3:list): list): list) = cons(x2, take(z, x3)),
           ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
           ax_nat: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
           :-
           goal: ∀xs (take(#c(Z: Nat), xs:list): list) = nil
      """

  val proof = Lemma( sequent ) {
    trivial
  }
}
