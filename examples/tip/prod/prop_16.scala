package gapt.examples.tip.prod

import gapt.expr._
import gapt.proofs.Context.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.AnalyticInductionProver

object prop_16 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )

  //Function constants
  ctx += hoc"'plus' :Nat>Nat>Nat"
  ctx += hoc"'even' :Nat>o"

  val sequent =
    hols"""
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_plus_0: ∀y (plus(#c(Z: Nat), y:Nat): Nat) = y,
        def_plus_1: ∀z ∀y (plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y)),
        def_even_0: even(#c(Z: Nat)): o,
        def_even_1: ¬even(S(#c(Z: Nat)): Nat),
        def_even_2: ∀z ((even(S(S(z:Nat): Nat)) → even(z)) ∧ (even(z) → even(S(S(z))))),
        constr_inj_0: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x even(plus(x:Nat, x): Nat)
  """

  val lemma_1 = (
    ( "ap1" -> hof"∀y plus(Z, y) = y" ) +:
    ( "ap2" -> hof"∀z ∀y plus(S(z), y) = S(plus(z, y))" ) +:
    Sequent() :+ ( "" -> hof"∀x ∀y plus(x, S(y)) = S(plus(x,y))" ) )

  val lemma_1_proof = AnalyticInductionProver.singleInduction( lemma_1, hov"x:Nat" )

  val proof = Lemma( sequent ) {
    cut( "lemma_1", hof"∀x ∀y plus(x, S(y)) = S(plus(x,y))" )
    insert( lemma_1_proof )
    allR; induction( hov"x:Nat" ); escargot.withDeskolemization.onAllSubGoals
  }
}
