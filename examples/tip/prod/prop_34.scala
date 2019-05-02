package gapt.examples.tip.prod

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.AnalyticInductionProver

object prop_34 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )

  //Function constants
  ctx += hoc"'plus' :Nat>Nat>Nat"
  ctx += hoc"'mult2' :Nat>Nat>Nat>Nat"
  ctx += hoc"'mult' :Nat>Nat>Nat"

  val sequent =
    hols"""
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_plus_0: ∀y (plus(#c(Z: Nat), y:Nat): Nat) = y,
        def_plus_1: ∀z ∀y (plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y)),
        def_mult2_0: ∀y ∀z (mult2(#c(Z: Nat), y:Nat, z:Nat): Nat) = z,
        def_mult2_1: ∀x2 ∀y ∀z (mult2(S(x2:Nat): Nat, y:Nat, z:Nat): Nat) = mult2(x2, y, plus(y, z)),
        def_mult_0: ∀y (mult(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat),
        def_mult_1: ∀z ∀y (mult(S(z:Nat): Nat, y:Nat): Nat) = plus(y, mult(z, y)),
        constr_inj_0: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x ∀y (mult(x:Nat, y:Nat): Nat) = mult2(x, y, #c(Z: Nat))
  """

  val plus_axioms = List(
    "ap1" -> hof"∀y plus(Z, y) = y",
    "ap2" -> hof"∀z ∀y plus(S(z), y) = S(plus(z, y))" )

  val mult_axioms = List(
    "am1" -> hof"∀y mult(Z, y) = Z",
    "am2" -> hof"∀z ∀y mult(S(z), y) = plus(y, mult(z, y))" )

  val mult2_axioms = List(
    "am21" -> hof"∀y ∀z mult2(Z, y, z) = z",
    "am22" -> hof"∀x2 ∀y ∀z mult2(S(x2), y, z) = mult2(x2, y, plus(y, z))" )

  val plus_right_s_goal = hof"!x !y plus(x,S(y)) = S(plus(x,y))"
  val plus_right_s = (
    plus_axioms ++:
    Sequent() :+ ( "" -> plus_right_s_goal ) )
  val plus_right_s_proof = AnalyticInductionProver.singleInduction( plus_right_s, hov"x:Nat" )

  val plus_z_neutral_goal = hof"!x plus(x,Z) = x"
  val plus_z_neutral = (
    plus_axioms ++:
    Sequent() :+ ( "" -> plus_z_neutral_goal ) )
  val plus_z_neutral_proof = AnalyticInductionProver.singleInduction( plus_z_neutral, hov"x:Nat" )

  val plus_comm_goal = hof"!x !y plus(x,y) = plus(y,x)"
  val plus_comm = (
    plus_axioms ++:
    ( "prs" -> plus_right_s_goal ) +:
    ( "pzn" -> plus_z_neutral_goal ) +: Sequent() :+ ( "goal" -> plus_comm_goal ) )
  val plus_comm_proof = Lemma( plus_comm ) {
    allR; induction( hov"x:Nat" )
    //- IB
    decompose
    rewrite ltr "ap1" in "goal"
    rewrite ltr "pzn" in "goal"; refl
    //- IS
    decompose
    rewrite ltr "ap2" in "goal"
    rewrite ltr "IHx_0" in "goal"
    rewrite ltr "prs" in "goal"; refl
  }

  val lemma_24_goal = hof"!x !y !z plus(x,plus(y,z)) = plus(plus(x,y),z)"
  val lemma_24 = ( plus_axioms ++: Sequent() :+ ( "" -> lemma_24_goal ) )
  val lemma_24_proof = AnalyticInductionProver.singleInduction( lemma_24, hov"x:Nat" )

  val cong_11_goal = hof"!x !y !z plus(mult(x,y),z) = mult2(x,y,z)"
  val cong_11 = (
    plus_axioms ++:
    mult_axioms ++:
    mult2_axioms ++:
    ( "l24" -> lemma_24_goal ) +:
    ( "pcm" -> plus_comm_goal ) +:
    Sequent() :+ ( "goal" -> cong_11_goal ) )
  val cong_11_proof = Lemma( cong_11 ) {
    allR; induction( hov"x:Nat" )
    //- IB
    decompose
    rewrite ltr "am1" in "goal"
    rewrite ltr "am21" in "goal"
    rewrite ltr "ap1" in "goal"; refl
    //- IS
    decompose
    rewrite ltr "am2" in "goal"
    rewrite ltr "am22" in "goal"
    rewrite ltr "pcm" in "goal" subst ( hov"y:Nat" -> le"mult(x_0:Nat,y:Nat)" )
    rewrite rtl "l24" in "goal"
    rewrite ltr "IHx_0" in "goal"; refl
  }

  val proof = Lemma( sequent ) {
    cut( "", plus_right_s_goal ); insert( plus_right_s_proof )
    cut( "", plus_z_neutral_goal ); insert( plus_z_neutral_proof )
    cut( "", lemma_24_goal ); insert( lemma_24_proof )
    cut( "", plus_comm_goal ); insert( plus_comm_proof )
    cut( "", cong_11_goal ); insert( cong_11_proof )
    escargot
  }

}
