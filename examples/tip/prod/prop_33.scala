package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.aip.AnalyticInductionProver

object prop_33 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_33.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val plus_axioms = List(
    "ap1" -> hof"∀y plus(Z, y) = y",
    "ap2" -> hof"∀z ∀y plus(S(z), y) = S(plus(z, y))"
  )

  val mult_axioms = List(
    "am1" -> hof"∀y mult(Z, y) = Z",
    "am2" -> hof"∀z ∀y mult(S(z), y) = plus(y, mult(z, y))"
  )

  val fac_axioms = List(
    "af1" -> hof"fac(Z) = S(Z)",
    "af2" -> hof"∀y fac(S(y)) = mult(S(y), fac(y))"
  )

  val qfac_axioms = List(
    "aq1" -> hof"∀y qfac(Z, y) = y",
    "aq2" -> hof"∀z ∀y qfac(S(z), y) = qfac(z, mult(S(z), y))"
  )

  val plus_right_s_goal = hof"!x !y plus(x,S(y)) = S(plus(x,y))"
  val plus_right_s = (
    plus_axioms ++:
    Sequent() :+ ( "" -> plus_right_s_goal )
  )
  val plus_right_s_proof = AnalyticInductionProver.singleInduction( plus_right_s, hov"x:Nat" )

  val plus_z_neutral_goal = hof"!x plus(x,Z) = x"
  val plus_z_neutral = (
    plus_axioms ++:
    Sequent() :+ ( "" -> plus_z_neutral_goal )
  )
  val plus_z_neutral_proof = AnalyticInductionProver.singleInduction( plus_z_neutral, hov"x:Nat" )

  val plus_comm_goal = hof"!x !y plus(x,y) = plus(y,x)"
  val plus_comm = (
    plus_axioms ++:
    ( "prs" -> plus_right_s_goal ) +:
    ( "pzn" -> plus_z_neutral_goal ) +: Sequent() :+ ( "goal" -> plus_comm_goal )
  )
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
    plus_axioms ++: mult_axioms ++: Sequent() :+ ( "" -> mult_one_right_id_goal )
  )
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
