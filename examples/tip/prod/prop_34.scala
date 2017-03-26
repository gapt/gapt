package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.aip.AnalyticInductionProver

object prop_34 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_34.smt2", getClass ) )
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

  val mult2_axioms = List(
    "am21" -> hof"∀y ∀z mult2(Z, y, z) = z",
    "am22" -> hof"∀x2 ∀y ∀z mult2(S(x2), y, z) = mult2(x2, y, plus(y, z))"
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
    Sequent() :+ ( "goal" -> cong_11_goal )
  )
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
