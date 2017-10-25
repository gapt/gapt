package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic.{ Lemma, TacticsProof, _ }

object prop_13 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )

  //Function constants
  ctx += hoc"'plus' :Nat>Nat>Nat"
  ctx += hoc"'half' :Nat>Nat"

  val sequent =
    hols"""
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_plus_0: ∀y (plus(#c(Z: Nat), y:Nat): Nat) = y,
        def_plus_1: ∀z ∀y (plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y)),
        def_half_0: (half(#c(Z: Nat)): Nat) = #c(Z: Nat),
        def_half_1: (half(S(#c(Z: Nat)): Nat): Nat) = #c(Z: Nat),
        def_half_2: ∀z (half(S(S(z:Nat): Nat)): Nat) = S(half(z)),
        constr_inj_0: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x (half(plus(x:Nat, x): Nat): Nat) = x
  """

  val theory = sequent.antecedent ++: Sequent()

  val hypothesis = hof"!x(!y plus(x, S(y)) = S(plus(x,y)) & half(plus(x,x)) = x)"

  val hypothesis_proof = Lemma( theory :+ "hyp" -> hypothesis ) {
    allR; induction( hov"x:Nat" )
    //- base case
    andR
    //-- base case: plus_s_comm
    allR
    rewrite.many ltr "def_plus_0" in "hyp"
    refl
    //-- base case: goal
    rewrite.many ltr "def_plus_0" in "hyp"
    axiomLog
    //- inductive case
    andL; andR
    //-- inductive case: plus_s_comm
    allR
    rewrite.many ltr "def_plus_1" in "hyp"
    rewrite.many ltr "IHx_0_0" in "hyp"
    refl
    //-- inductive case: goal
    rewrite.many ltr "def_plus_1" in "hyp"
    rewrite.many ltr "IHx_0_0" in "hyp"
    rewrite.many ltr "def_half_2" in "hyp"
    rewrite.many ltr "IHx_0_1" in "hyp"
    refl
  }

  val proof = Lemma( sequent ) {
    cut( "hyp", hypothesis ); insert( hypothesis_proof )
    escargot
  }
}