package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.gaptic._

object prop_59 extends TacticsProof {

  // Inductive types
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :Nat>list>list" )

  //Function constants
  ctx += hoc"'last' :list>Nat"
  ctx += hoc"'append' :list>list>list"

  val sequent =
    hols"""
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_head: ∀x0 ∀x1 (head(cons(x0:Nat, x1:list): list): Nat) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:Nat, x1:list): list): list) = x1,
        def_last_0: (last(nil:list): Nat) = #c(Z: Nat),
        def_last_1: ∀y (last(cons(y:Nat, nil:list): list): Nat) = y,
        def_last_2: ∀y   ∀x2   ∀x3   (last(cons(y:Nat, cons(x2:Nat, x3:list): list)): Nat) = last(cons(x2, x3)),
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:Nat, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        constr_inj_0: ∀y0 ¬#c(Z: Nat) = S(y0:Nat),
        constr_inj_1: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
        :-
        goal: ∀xs ∀ys ((ys:list) = nil → (last(append(xs:list, ys): list): Nat) = last(xs))
  """

  val proof_1 = Lemma( sequent ) {
    introUnivsExcept( 0 )
    treeGrammarInduction
  }
}
