package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics.AnalyticInductionTactic._

object prop_49 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_49.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val listType = bench.datatypes( 1 )

  val list_projector_axioms = Seq(
    "alp1" -> hof"∀x0 ∀x1 head(cons(x0, x1)) = x0",
    "alp2" -> hof"∀x0 ∀x1 tail(cons(x0, x1)) = x1" )

  val append_axioms = Seq(
    "ap1" -> hof"∀y append(nil, y) = y",
    "ap2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" )
  val butlastconcat_axioms = Seq(
    "ablc1" -> hof"∀x butlastConcat(x, nil) = butlast(x)",
    "ablc2" -> hof"∀x ∀z ∀x2 butlastConcat(x, cons(z, x2)) = append(x, butlast(cons(z, x2)))" )

  val butlast_axioms = Seq(
    "abl1" -> hof"∀y butlast(cons(y, nil)) = nil",
    "abl2" -> hof"∀y ∀x2 ∀x3 butlast(cons(y, cons(x2, x3))) = cons(y, butlast(cons(x2, x3)))" )

  val list_dca_goal = hof"!xs (xs = nil ∨ xs = cons(head(xs),tail(xs)))"
  val list_dca = (
    ( "pl0" -> hof"∀x0 ∀x1 head(cons(x0, x1)) = x0" ) +:
    ( "pl1" -> hof"∀x0 ∀x1 tail(cons(x0, x1)) = x1" ) +:
    Sequent() :+
    "goal" -> list_dca_goal )
  val list_dca_proof = Lemma( list_dca ) {
    allR; induction( hov"xs:list" ); escargot; escargot
  }

  val append_nil_goal = hof"!xs append(xs,nil) = xs"
  val append_nil_proof = Lemma( append_axioms ++:
    Sequent() :+
    ( "goal" -> append_nil_goal ) ) {
    analyticInduction withAxioms sequentialAxioms.forVariables( hov"xs:list" ).forLabel( "goal" )
  }

  val butlast_append_nil_goal = hof"!xs !x butlast(append(xs,cons(x,nil))) = xs"
  val butlast_append_nil_proof = Lemma( append_axioms ++: butlast_axioms ++:
    ( "dca" -> list_dca_goal ) +:
    Sequent() :+
    ( "goal" -> butlast_append_nil_goal ) ) {
    allR; induction( hov"xs:list" )
    escargot
    allR
    allL( "dca", le"xs_0:list" )
    orL
    escargot
    escargot
  }

  val append_inner_shift_goal = hof"!xs !ys !x append(xs, cons(x,ys)) = append(append(xs,cons(x,nil)),ys)"
  val append_inner_shift_proof = Lemma( append_axioms ++:
    Sequent() :+
    ( "goal" -> append_inner_shift_goal ) ) {
    analyticInduction withAxioms sequentialAxioms.forVariables( hov"xs:list" ).forLabel( "goal" )
  }

  val butlast_inner_append_goal = hof"!ys !xs !y butlast(append(xs, cons(y,ys))) = append(xs, butlast(cons(y,ys)))"
  val butlast_inner_append_proof = Lemma( butlast_axioms ++: append_axioms ++:
    ( "lem_api" -> append_inner_shift_goal ) +:
    ( "lem_ban" -> butlast_append_nil_goal ) +:
    ( "lem_ani" -> append_nil_goal ) +:
    Sequent() :+
    ( "goal" -> butlast_inner_append_goal ) ) {
    analyticInduction withAxioms sequentialAxioms.forVariables( hov"ys:list" ).forLabel( "goal" )
  }

  val proof = Lemma( sequent ) {
    cut( "", list_dca_goal ); insert( list_dca_proof )
    cut( "", append_inner_shift_goal ); insert( append_inner_shift_proof )
    cut( "append_lemma", append_nil_goal ); insert( append_nil_proof )
    cut( "", butlast_append_nil_goal ); insert( butlast_append_nil_proof )
    cut( "main_lemma", butlast_inner_append_goal ); insert( butlast_inner_append_proof )
    allR; allR
    induction( hov"ys:list" )
    rewrite ltr "h7" in "goal"
    rewrite ltr "append_lemma" in "goal"
    refl
    rewrite ltr "h8" in "goal"
    rewrite ltr "main_lemma" in "goal"
    refl
  }
}
