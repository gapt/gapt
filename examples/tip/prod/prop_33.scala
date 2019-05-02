package gapt.examples.tip.prod

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.AnalyticInductionProver

object prop_33 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )

  //Function constants
  ctx += hoc"'plus' :Nat>Nat>Nat"
  ctx += hoc"'one' :Nat"
  ctx += hoc"'mult' :Nat>Nat>Nat"
  ctx += hoc"'qfac' :Nat>Nat>Nat"
  ctx += hoc"'fac' :Nat>Nat"

  val sequent =
    hols"""
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_plus_0: ∀y (plus(#c(Z: Nat), y:Nat): Nat) = y,
        def_plus_1: ∀z ∀y (plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y)),
        def_one_0: (one:Nat) = S(#c(Z: Nat)),
        def_mult_0: ∀y (mult(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat),
        def_mult_1: ∀z ∀y (mult(S(z:Nat): Nat, y:Nat): Nat) = plus(y, mult(z, y)),
        def_qfac_0: ∀y (qfac(#c(Z: Nat), y:Nat): Nat) = y,
        def_qfac_1: ∀z ∀y (qfac(S(z:Nat): Nat, y:Nat): Nat) = qfac(z, mult(S(z), y)),
        def_fac_0: (fac(#c(Z: Nat)): Nat) = S(#c(Z: Nat)),
        def_fac_1: ∀y (fac(S(y:Nat): Nat): Nat) = mult(S(y), fac(y)),
        constr_inj_0: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x (fac(x:Nat): Nat) = qfac(x, one:Nat)
  """

  val plus_axioms = List(
    "ap1" -> hof"∀y plus(Z, y) = y",
    "ap2" -> hof"∀z ∀y plus(S(z), y) = S(plus(z, y))" )

  val mult_axioms = List(
    "am1" -> hof"∀y mult(Z, y) = Z",
    "am2" -> hof"∀z ∀y mult(S(z), y) = plus(y, mult(z, y))" )

  val fac_axioms = List(
    "af1" -> hof"fac(Z) = S(Z)",
    "af2" -> hof"∀y fac(S(y)) = mult(S(y), fac(y))" )

  val qfac_axioms = List(
    "aq1" -> hof"∀y qfac(Z, y) = y",
    "aq2" -> hof"∀z ∀y qfac(S(z), y) = qfac(z, mult(S(z), y))" )

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

  val plus_assoc_goal = hof"!x !y !z plus(plus(x,y),z) = plus(x,plus(y,z))"
  val plus_assoc = ( plus_axioms ++:
    Sequent() :+ ( "goal" -> plus_assoc_goal ) )
  val plus_assoc_proof = AnalyticInductionProver.singleInduction( plus_assoc, hov"x:Nat" )

  val mult_z_zero_goal = hof"!x mult(x,Z) = Z"
  val mult_z_zero = ( plus_axioms ++: mult_axioms ++:
    Sequent() :+ ( "goal" -> mult_z_zero_goal ) )
  val mult_z_zero_proof = AnalyticInductionProver.singleInduction( mult_z_zero, hov"x:Nat" )

  val mult_dist_law_1_goal = hof"!x !y !z mult(x, plus(y,z)) = plus(mult(x,y),mult(x,z))"
  val mult_dist_law_1 = ( plus_axioms ++: mult_axioms ++:
    ( "pcm" -> plus_comm_goal ) +:
    ( "pas" -> plus_assoc_goal ) +:
    Sequent() :+ ( "goal" -> mult_dist_law_1_goal ) )
  val mult_dist_law_1_proof = Lemma( mult_dist_law_1 ) {
    allR; induction( hov"x:Nat" )
    decompose
    rewrite.many ltr "am1" in "goal"
    rewrite.many ltr "ap1" in "goal"; refl
    //- IS
    decompose
    rewrite.many ltr "am2" in "goal"
    escargot
  }

  val mult_dist_law_2_goal = hof"!x !y !z mult(plus(x,y),z) = plus(mult(x,z),mult(y,z))"
  val mult_dist_law_2 = ( plus_axioms ++: mult_axioms ++:
    ( "plus_assoc" -> plus_assoc_goal ) +:
    Sequent() :+ ( "goal" -> mult_dist_law_2_goal ) )

  val mult_dist_law_2_proof = Lemma( mult_dist_law_2 ) {
    allR; induction( hov"x:Nat" )
    //- IB
    decompose
    rewrite.many ltr "am1" in "goal"
    rewrite.many ltr "ap1" in "goal"
    refl
    //- IS
    decompose
    rewrite.many ltr "am2" in "goal"
    rewrite.many ltr "ap2" in "goal"
    rewrite.many ltr "plus_assoc" in "goal"
    rewrite.many rtl "IHx_0" in "goal"
    rewrite.many ltr "am2" in "goal"
    refl
  }

  val mult_one_right_id_goal = hof"!x mult(x, S(Z)) = x"
  val mult_one_right_id = (
    plus_axioms ++: mult_axioms ++: Sequent() :+ ( "" -> mult_one_right_id_goal ) )
  val mult_one_right_id_proof = AnalyticInductionProver.singleInduction( mult_one_right_id, hov"x:Nat" )

  val mult_comm_goal = hof"!x !y mult(x,y) = mult(y,x)"
  val mult_comm = ( plus_axioms ++: mult_axioms ++:
    ( "mzz" -> mult_z_zero_goal ) +:
    ( "md1" -> mult_dist_law_1_goal ) +:
    ( "m1i" -> mult_one_right_id_goal ) +:
    Sequent() :+ ( "goal" -> mult_comm_goal ) )
  val mult_comm_proof = Lemma( mult_comm ) {
    allR; induction( hov"x:Nat" )
    //- IB
    decompose
    rewrite ltr "am1" in "goal"
    escargot
    //- IS
    decompose
    rewrite ltr "am2" in "goal"
    rewrite ltr "IHx_0" in "goal"
    allL( "m1i", le"y:Nat" ); rewrite rtl "m1i_0" in "goal"
    rewrite rtl "md1" in "goal"
    rewrite ltr "ap2" in "goal"
    rewrite ltr "ap1" in "goal"; refl
  }

  val lemma_23_goal = hof"!x !y !z mult(x,mult(y,z)) = mult(mult(x,y),z)"
  val lemma_23 = ( plus_axioms ++: mult_axioms ++:
    ( "dl2" -> mult_dist_law_2_goal ) +:
    Sequent() :+ ( "goal" -> lemma_23_goal ) )

  val lemma_23_proof = Lemma( lemma_23 ) {
    allR; induction( hov"x:Nat" )
    escargot
    allR; allR
    rewrite.many ltr "am2" in "goal"
    rewrite ltr "IHx_0" in "goal"
    rewrite ltr "dl2" in "goal"
    refl
  }

  val cong_10_goal = hof"!x !y mult(fac(x),y) = qfac(x,y)"

  val cong_10 = ( plus_axioms ++: mult_axioms ++: fac_axioms ++: qfac_axioms ++:
    ( "l23" -> lemma_23_goal ) +:
    ( "lea" -> plus_z_neutral_goal ) +:
    ( "lec" -> mult_comm_goal ) +:
    ( "led" -> mult_dist_law_2_goal ) +:
    Sequent() :+ ( "goal" -> cong_10_goal ) )

  val cong_10_proof = Lemma( cong_10 ) {
    allR; induction( hov"x:Nat" )
    //- IB
    allR
    rewrite ltr "af1" in "goal"
    rewrite ltr "aq1" in "goal"
    rewrite ltr "am2" in "goal"
    rewrite ltr "am1" in "goal"
    escargot
    //- IS
    allR
    rewrite ltr "af2" in "goal"
    rewrite ltr "aq2" in "goal"
    rewrite.many ltr "am2" in "goal"
    rewrite rtl "IHx_0" in "goal"
    escargot
  }

  val proof = Lemma( sequent ) {
    cut( "", plus_right_s_goal ); insert( plus_right_s_proof )
    cut( "", plus_z_neutral_goal ); insert( plus_z_neutral_proof )
    cut( "", plus_comm_goal ); insert( plus_comm_proof )
    cut( "", plus_assoc_goal ); insert( plus_assoc_proof )
    cut( "", mult_z_zero_goal ); insert( mult_z_zero_proof )
    cut( "", mult_dist_law_1_goal ); insert( mult_dist_law_1_proof )
    cut( "", mult_dist_law_2_goal ); insert( mult_dist_law_2_proof )
    cut( "", mult_one_right_id_goal ); insert( mult_one_right_id_proof )
    cut( "", mult_comm_goal ); insert( mult_comm_proof )
    cut( "", lemma_23_goal ); insert( lemma_23_proof )
    cut( "", cong_10_goal ); insert( cong_10_proof )
    escargot
  }

}
