package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._

object prop_16 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:Nat>list>list" )
  ctx += hoc"head:list>Nat"
  ctx += hoc"tail:list>list"

  ctx += hoc"last:list>Nat"

  val sequent = hols"""
                      def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
                      def_head: ∀x0 ∀x1 (head(cons(x0:Nat, x1:list): list): Nat) = x0,
                      def_tail: ∀x0 ∀x1 (tail(cons(x0:Nat, x1:list): list): list) = x1,
                      def_last_1: (last(nil:list): Nat) = #c(Z: Nat),
                      def_last_2: ∀y (last(cons(y:Nat, nil:list): list): Nat) = y,
                      def_last_3: ∀y ∀x2 ∀x3 (last(cons(y:Nat, cons(x2:Nat, x3:list): list)): Nat) = last(cons(x2, x3)),
                      ax_nat_1:∀y0 ¬#c(Z: Nat) = S(y0:Nat),
                      ax_list_1:∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
                      :-
                      goal: ∀x ∀xs ((xs:list) = nil → (last(cons(x:Nat, xs): list): Nat) = x)
    """

  val proof = Lemma( sequent ) {
    allR
    allR
    impR
    eql( "goal_0", "goal_1" )
    allL( "def_last_2", le"x:Nat" )
    axiomLog
  }
}
