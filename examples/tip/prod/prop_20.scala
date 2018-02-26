package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.aip.AnalyticInductionProver

object prop_20 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list" )
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )

  //Function constants
  ctx += hoc"'length' :list>Nat"
  ctx += hoc"'even' :Nat>o"
  ctx += hoc"'append' :list>list>list"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_length_0: (length(nil:list): Nat) = #c(Z: Nat),
        def_length_1: ∀y ∀xs (length(cons(y:sk, xs:list): list): Nat) = S(length(xs)),
        def_even_0: even(#c(Z: Nat)): o,
        def_even_1: ¬even(S(#c(Z: Nat)): Nat),
        def_even_2: ∀z ((even(S(S(z:Nat): Nat)) → even(z)) ∧ (even(z) → even(S(S(z))))),
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        constr_inj_0: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
        constr_inj_1: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x even(length(append(x:list, x): list): Nat)
  """

  val lemma = (
    ( "" -> hof"length(nil) = Z" ) +:
    ( "" -> hof"∀y ∀xs length(cons(y, xs)) = S(length(xs))" ) +:
    ( "" -> hof"∀y append(nil, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    Sequent() :+ ( "lemma" -> hof"∀xs ∀ys ∀y length(append(xs, cons(y,ys))) = S(length(append(xs, ys)))" ) )

  val lemma_proof = AnalyticInductionProver.singleInduction( lemma, hov"xs:list" )

  val proof = Lemma( sequent ) {
    cut( "lemma", hof"∀xs ∀ys ∀y length(append(xs, cons(y,ys))) = S(length(append(xs, ys)))" )
    insert( lemma_proof )
    allR; induction( hov"x:list" ); escargot.withDeskolemization.onAllSubGoals
  }
}
