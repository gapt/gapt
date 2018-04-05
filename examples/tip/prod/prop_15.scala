package gapt.examples.tip.prod

import gapt.expr._
import gapt.proofs.Context.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic.{ Lemma, TacticsProof, _ }

object prop_15 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )

  //Function constants
  ctx += hoc"'plus' :Nat>Nat>Nat"

  val sequent =
    hols"""
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_plus_0: ∀y (plus(#c(Z: Nat), y:Nat): Nat) = y,
        def_plus_1: ∀z ∀y (plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y)),
        constr_inj_0: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x (plus(x:Nat, S(x): Nat): Nat) = S(plus(x, x))
  """

  val theory = sequent.antecedent ++: Sequent()

  val proof = Lemma( sequent ) {
    cut( "lemma", hof"!x!y plus(x, S(y)) = S(plus(x,y))" );
    //- proof lemma
    forget( "goal" )
    allR; induction( hov"x:Nat" )
    //-- BC lemma
    allR
    rewrite.many ltr "def_plus_0" in "lemma"
    refl
    //-- IC lemma
    allR
    rewrite.many ltr "def_plus_1" in "lemma"
    rewrite.many ltr "IHx_0" in "lemma"
    refl
    //- proof goal
    allR;
    rewrite.many ltr "lemma" in "goal"
    refl
  }
}