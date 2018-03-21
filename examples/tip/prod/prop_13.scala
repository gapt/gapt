package gapt.examples.tip.prod

import gapt.expr._
import gapt.proofs.Context.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic.{ Lemma, TacticsProof, _ }

object prop_13 extends TacticsProof {

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

  val lem = hof"!y ( plus(x, S(y)) = S(plus(x,y)) & half(plus(x,x)) = x )"

  val lem_proof = Lemma( theory :+ "lem" -> lem ) {
    induction( hov"x:Nat" )
    //- base case
    allR; andR
    //-- base case: plus_s_comm
    rewrite.many ltr "def_plus_0" in "lem"
    refl
    //-- base case: goal
    rewrite.many ltr "def_plus_0" in "lem"
    rewrite.many ltr "def_half_0" in "lem"
    refl
    //- inductive case
    allR; andR
    //-- inductive case: plus_s_comm
    rewrite.many ltr "def_plus_1" in "lem"
    allL( "IHx_0", le"y:Nat" )
    quasiprop
    //-- inductive case: goal
    rewrite.many ltr "def_plus_1" in "lem"
    allL( "IHx_0", le"x_0:Nat" ); andL
    rewrite.many ltr "IHx_0_0_0" in "lem"
    rewrite.many ltr "def_half_2" in "lem"
    quasiprop
  }

  val proof = Lemma( sequent ) {
    allR; cut( "lem", lem ); insert( lem_proof )
    escargot.withDeskolemization
  }
}

